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

// Incremental version
#if 1
class imax : public propagator, public prop_inst<imax> {
  static watch_result wake_z(void* ptr, int k) {
    imax* p(static_cast<imax*>(ptr));
    p->z_change |= k;
    p->queue_prop();
    return Wt_Keep;
  }

  static watch_result wake_x(void* ptr, int xi) {
    imax* p(static_cast<imax*>(ptr));
    assert((xi>>1) < p->xs.size());
    if(xi&1) { // UB
      if(xi>>1 == p->ub_supp) {
        p->supp_change = E_UB;
        p->queue_prop();
      }
    } else {
      if(!p->lb_change.elem(xi>>1))
        p->lb_change.add(xi>>1);
      p->queue_prop();
    }
    return Wt_Keep;
  }

  void ex_z_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t z_lb = z.lb_of_pval(p);
    expl.push(xs[xi] < z_lb);
  }

  void ex_z_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t z_ub = z.ub_of_pval(p); 
    for(intvar x : xs) {
      expl.push(x > z_ub);
    }
  }

  void ex_xi_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t x_lb = xs[xi].lb_of_pval(p);
    intvar::val_t sep = std::max(x_lb, sep_val);
    expl.push(z < sep);
    for(int x : irange(xi)) {
      expl.push(xs[x] >= sep);
    }
    for(int x : irange(xi+1,xs.size())) {
      expl.push(xs[x] >= sep);
    }
  }

  void ex_xi_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t x_ub = xs[xi].ub_of_pval(p);
    expl.push(z > x_ub);
  }

public:
  imax(solver_data* s, intvar _z, vec<intvar>& _xs)
    : propagator(s), z(_z), xs(_xs),
      sep_val(lb(z)), z_change(0), supp_change(0) { 
    z.attach(E_LB, watch_callback(wake_z, this, 0, true));
    z.attach(E_UB, watch_callback(wake_z, this, 1, true));

    lb_supp = ub_supp = 0;
    int lb = xs[lb_supp].lb(s);
    int ub = xs[ub_supp].ub(s);
    for(int ii = 0; ii < xs.size(); ii++) {
      if(xs[ii].lb(s) < lb) {
        lb_supp = ii;
        lb = xs[ii].lb(s);
      }
      if(xs[ii].ub(s) > ub) {
        ub_supp = ii;
        ub = xs[ii].ub(s);
      }
      xs[ii].attach(E_LB, watch_callback(wake_x, this, ii<<1, true));
      xs[ii].attach(E_UB, watch_callback(wake_x, this, (ii<<1)|1, true));
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

  bool check_sat(ctx_t& ctx) {
    bool has_candidate = false;
    int z_lb = z.lb(ctx);
    int z_ub = z.ub(ctx);
    for(intvar x : xs) {
      if(x.lb(ctx) > z_ub)
        return false;
      if(x.ub(ctx) >= z_lb)
        has_candidate = true;
    }
    return has_candidate;
  }
  bool check_unsat(ctx_t& ctx) {
    return !check_sat(ctx);
  }

  inline bool propagate_z_ub(vec<clause_elt>& confl, bool& mm_trailed) {
    unsigned int seen_var = ub_supp;
    int seen_ub = xs[ub_supp].ub(s);
    for(int xi : maybe_max) {
      assert(xi < xs.size());
      if(seen_ub < xs[xi].ub(s)) {
        seen_var = xi;
        seen_ub = xs[xi].ub(s);
      }
    }

    if(seen_ub < ub(z)) {
      /*
      expl_builder e(s->persist.alloc_expl(1 + xs.size()));
      for(intvar x : xs)
        e.push(x > seen_ub);
      if(!z.set_ub(seen_ub, *e))
        */
      if(!set_ub(z, seen_ub, ex_thunk(ex<&P::ex_z_ub>, 0)))
        return false;
    }
    if(seen_var != ub_supp)
      trail_change(s->persist, ub_supp, seen_var);

    return true; 
  }

  inline bool propagate_xs_lb(vec<clause_elt>& confl, bool& mm_trailed) {
    unsigned int *xi = maybe_max.begin();
    int z_lb = lb(z);
    while(xi != maybe_max.end()) {
      if(xs[*xi].ub(s) < z_lb) {
        // xs[*xi] cannot be the maximum
        if(!mm_trailed) {
          mm_trailed = true;
          trail_push(s->persist, maybe_max.sz);
        }
        if(sep_val <= xs[*xi].ub(s))
          sep_val = xs[*xi].ub(s)+1;
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
    EX_PUSH(confl, z < z_lb);
    for(intvar x : xs)
      EX_PUSH(confl, x >= z_lb);
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
    /*
    expl_builder e(s->persist.alloc_expl(1 + xs.size()));
    e.push(z < z_lb);
    for(int ii = 0; ii < xs.size(); ii++) {
        if(ii != supp)
          e.push(xs[ii] >= z_lb);
    }
    if(!xs[supp].set_lb(z_lb, *e))
    */
    if(sep_val > lb(z))
      sep_val = lb(z);
    if(!set_lb(xs[supp], z_lb, ex_thunk(ex<&P::ex_xi_lb>, supp)))
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
      int z_ub = ub(z);
      for(int ii : maybe_max) {
        if(z_ub < xs[ii].ub(s)) {
          // if(!xs[ii].set_ub(z_ub, z > z_ub))
          if(!set_ub(xs[ii], z_ub, ex_thunk(ex<&P::ex_xi_ub>, ii)))
            return false; 
        }
      }
    }

    // forall x, lb(z) >= lb(x).
    int z_lb = lb(z);
    for(int xi : lb_change) {
      if(xs[xi].lb(s) > z_lb) {
        z_lb = xs[xi].lb(s);
        // if(!z.set_lb(z_lb, xs[xi] < z_lb))
        if(!set_lb(z, z_lb, ex_thunk(ex<&P::ex_z_lb>, xi)))
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

  /*
  bool check_sat(ctx_t& ctx) {
    int zlb = INT_MIN; 
    int zub = INT_MIN;
    for(intvar x : xs) {
      zlb = std::max(zlb, (int) x.lb(ctx));
      zub = std::max(zub, (int) x.ub(ctx));
    }
    return zlb <= z.ub(ctx) && z.lb(ctx) <= zub;
  }
  */

  void root_simplify(void) { }

  void cleanup(void) {
    z_change = 0;
    supp_change = 0;
    lb_change.clear();
    is_queued = false;
  }

protected:
  intvar z;
  vec<intvar> xs;

  // Persistent state
  unsigned int lb_supp;
  unsigned int ub_supp;
  p_sparseset maybe_max; // The set of vars (possibly) above lb(z)
  intvar::val_t sep_val;

  // Transient state
  char z_change;
  char supp_change;
  boolset lb_change;
};
#else
// FIXME: Finish implementing
class max_lb : public propagator, public prop_inst<max_lb> {
  enum { S_Active = 1, S_Red = 2 };

  inline void add_cb(int xi, pid_t p) {
    if(!attached[xi]) {
      s->watch_callbacks[p].push(watch<&P::watch_act>, 0, Wt_IDEM);
      attached[xi] = true;
    }
  }

  watch_result watch_xi(int xi) {
      // Update watches
        
      // No watches remaining.
      trail_change(s->persist, status, (char) S_Active);
      add_cb(0, xs[0]^1); // ub(x) decreases
      add_cb(1, z); // lb(z) increases
  }

  watch_result watch_act(int xi) {
    if(!(status&S_Active)) {
      attached[xi] = 0;
      return Wt_Drop; 
    }

    queue_prop(); 
  }

  void ex_z(int is_z, pval_t pval, vec<clause_elt>& expl) {
    pval_t v;
    if(is_z) {
      // Explaining ub(z)
      v = pval_inv(pval);
      expl.push(ge_lit(xs[xi], v+1));
    } else {
      // Explaining lb(xs[0])
      v = pval;
      expl.push(le_lit(z, v-1));
    }
    pval_t gap = std::max(v, sep+1);
    for(int ii = 1; ii < xs.size(); ii++)
      expl.push(ge_lit(xs[ii], gap));
  }

public:
  malb(xsolver_data* _s, vec<pid_t>& _xs, pid_t z)
    : propagator(_s), xs(_xs), z(_z) {
    for(int ii : irange(2))
      attached[ii] = 0; 
  }
  bool propagate(void) {
    
  }

  void simplify_at_root(void) {
    
  }

  vec<pid_t> xs;
  pid_t z;

  pval_t sep;
  
  char status;

  // Keeping track of active watches
  bool attached[2];
};
#endif

void imax_decomp(solver_data* s, intvar z, vec<intvar>& xs) {
  vec<clause_elt> elts;
  for(int k : irange(z.lb(s), z.ub(s)+1)) {
    elts.clear();
    elts.push(z <= k);
    for(intvar x : xs) {
      add_clause(s, x < k, z >= k);
      elts.push(x > k);
    }
    add_clause(*s, elts);
  }
  
  elts.clear();
  for(intvar x : xs) {
    if(x.ub(s) > z.ub(s))
      enqueue(*s, x <= z.ub(s), reason());
    elts.push(x >= z.lb(s));
  }
  add_clause(*s, elts);
}

bool int_max(solver_data* s, intvar z, vec<intvar>& xs, patom_t r) {
  // FIXME: Choose whether to use propagator or decomposition
  // imax_decomp(s, z, xs);
  if(!s->state.is_entailed_l0(r))
    GEAS_WARN("Half-reified int_max not yet implemented.");

  // new imax(s, z, xs);
  // return true;
  return imax::post(s, z, xs);
}



}
