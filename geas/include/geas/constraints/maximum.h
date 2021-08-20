#include <algorithm>
#include <climits>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/solver/solver_data.h>
#include <geas/vars/intvar.h>
#include <geas/mtl/bool-set.h>
#include <geas/mtl/p-sparse-set.h>
#include <geas/utils/interval.h>

namespace geas {

// Templated version of max propagator.
template<class Val, class Var>
class maximum : public propagator, public prop_inst< maximum<Val, Var> > {
  typedef maximum P;
  typedef prop_inst< maximum<Val, Var> > I;

  watch_result wake_z(int k) {
    z_change |= k;
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_x(int xi) {
    assert((xi>>1) < xs.size());
    unsigned int idx(xi>>1);
    if(xi&1) { // UB
      if(idx == ub_supp) {
        supp_change = E_UB;
        queue_prop();
      }
    } else {
      if(!lb_change.elem(idx))
        lb_change.add(idx);
      queue_prop();
    }
    return Wt_Keep;
  }

  void ex_z_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    Val z_lb = z.lb_of_pval(p);
    expl.push(xs[xi] < z_lb);
  }

  void ex_z_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    Val z_ub = z.ub_of_pval(p); 
    for(const Var& x : xs) {
      expl.push(x > z_ub);
    }
  }

  void ex_xi_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    Val x_lb = xs[xi].lb_of_pval(p);
    Val sep = std::max(x_lb, sep_val);
    expl.push(z < sep);
    for(int x : irange(xi)) {
      expl.push(xs[x] >= sep);
    }
    for(int x : irange(xi+1,xs.size())) {
      expl.push(xs[x] >= sep);
    }
  }

  void ex_xi_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    Val x_ub = xs[xi].ub_of_pval(p);
    expl.push(z > x_ub);
  }

public:
  maximum(solver_data* s, Var _z, vec<Var>& _xs)
    : propagator(s), z(_z), xs(_xs),
      sep_val(lb(z)), z_change(0), supp_change(0) { 
    z.attach(E_LB, this->template watch<&P::wake_z>(0, I::Wt_IDEM));
    z.attach(E_UB, this->template watch<&P::wake_z>(1, I::Wt_IDEM));

    lb_supp = ub_supp = 0;
    Val lb = xs[lb_supp].lb(s);
    Val ub = xs[ub_supp].ub(s);
    for(int ii = 0; ii < xs.size(); ii++) {
      if(xs[ii].lb(s) < lb) {
        lb_supp = ii;
        lb = xs[ii].lb(s);
      }
      if(xs[ii].ub(s) > ub) {
        ub_supp = ii;
        ub = xs[ii].ub(s);
      }
      xs[ii].attach(E_LB, this->template watch<&P::wake_x>(ii<<1, I::Wt_IDEM));
      xs[ii].attach(E_UB, this->template watch<&P::wake_x>((ii<<1)|1, I::Wt_IDEM));
    }

    maybe_max.growTo(xs.size());
    for(int xi : irange(0, xs.size()))
      maybe_max.insert(xi);

    lb_change.growTo(xs.size()); 
  }

  inline void mm_remove(int k, bool& mm_trailed) {
    if(!mm_trailed)
      trail_push(s->persist, maybe_max.sz);
    mm_trailed = true;
    maybe_max.remove(k);
  }

  inline bool propagate_z_ub(vec<clause_elt>& confl, bool& mm_trailed) {
    unsigned int seen_var = ub_supp;
    Val seen_ub = xs[ub_supp].ub(s);
    for(int xi : maybe_max) {
      assert(xi < xs.size());
      if(seen_ub < xs[xi].ub(s)) {
        seen_var = xi;
        seen_ub = xs[xi].ub(s);
      }
    }

    if(seen_ub < ub(z)) {
      if(!enqueue(*s, z <= seen_ub, this->template expl<&P::ex_z_ub>(0)))
        return false;
    }
    if(seen_var != ub_supp)
      trail_change(s->persist, ub_supp, seen_var);

    return true; 
  }

  inline bool propagate_xs_lb(vec<clause_elt>& confl, bool& mm_trailed) {
    unsigned int *xi = maybe_max.begin();
    Val z_lb = lb(z);
    while(xi != maybe_max.end()) {
      if(xs[*xi].ub(s) < z_lb) {
        // xs[*xi] cannot be the maximum
        if(!mm_trailed) {
          mm_trailed = true;
          trail_push(s->persist, maybe_max.sz);
        }
        if(sep_val <= xs[*xi].ub(s))
          sep_val = xs[*xi].ub(s)+1; // FIXME: Only for ints.
        maybe_max.remove(*xi);
      } else {
        // lb(z) won't change anyway
        if(xs[*xi].lb(s) == z_lb)
          return true;

        goto first_lb_found;
      }
    }
    // Every variable is below lb_max.
    // Set up conflict and bail
    confl.push(z < z_lb);
    for(const Var& x : xs)
      confl.push(x >= z_lb);
    return false;

first_lb_found:
    unsigned int supp = *xi;
    ++xi;
    while(xi != maybe_max.end()) {
      if(xs[*xi].ub(s) < z_lb) {
        if(!mm_trailed) {
          mm_trailed = true;
          trail_push(s->persist, maybe_max.sz);
        }
        if(sep_val <= xs[*xi].ub(s))
          sep_val = xs[*xi].ub(s)+1;
        maybe_max.remove(*xi);
      } else {
        // Second support found
        return true;
      }
    }
    // Exactly one support found
    assert(xs[supp].lb(s) < z_lb);

    if(sep_val > lb(z))
      sep_val = lb(z);
    if(!set_lb(xs[supp], z_lb, this->template expl<&P::ex_xi_lb>(supp)))
      return false;

    return true;
  }

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cout << "[[Running imax]]" << std::endl;
#endif
    bool maybe_max_trailed = false;
    
    // forall x, ub(x) <= ub(z).
    if(z_change&E_UB) {
      Val z_ub = ub(z);
      for(int ii : maybe_max) {
        if(z_ub < xs[ii].ub(s)) {
          // if(!xs[ii].set_ub(z_ub, z > z_ub))
          if(!enqueue(*s, xs[ii] <= z_ub, this->template expl<&P::ex_xi_ub>(ii)))
            return false; 
        }
      }
    }

    // forall x, lb(z) >= lb(x).
    Val z_lb = lb(z);
    for(int xi : lb_change) {
      if(xs[xi].lb(s) > z_lb) {
        z_lb = xs[xi].lb(s);
        // if(!z.set_lb(z_lb, xs[xi] < z_lb))
        if(!enqueue(*s, z >= z_lb, this->template expl<&P::ex_z_lb>(xi)))
          return false;
      }
    }

    if(supp_change&E_UB) {
      if(!propagate_z_ub(confl, maybe_max_trailed))
        return false;
    }

    if(z_change&E_LB) {
      // Identify if any variable LBs must change
      if(!propagate_xs_lb(confl, maybe_max_trailed))
        return false;
    }
    return true;
  }

  bool check_sat(void) {
    Val zlb = lb(xs[0]);
    Val zub = ub(xs[0]);
    for(const Var& x : xs.tail()) {
      zlb = std::max(zlb, (Val) lb(x));
      zub = std::max(zub, (Val) ub(x));
    }
    return zlb <= ub(z) && lb(z) <= zub;
  }

  void root_simplify(void) { }

  void cleanup(void) {
    z_change = 0;
    supp_change = 0;
    lb_change.clear();
    is_queued = false;
  }

protected:
  Var z;
  vec<Var> xs;

  // Persistent state
  unsigned int lb_supp;
  unsigned int ub_supp;
  p_sparseset maybe_max; // The set of vars (possibly) above lb(z)
  Val sep_val;

  // Transient state
  char z_change;
  char supp_change;
  boolset lb_change;
};

}
