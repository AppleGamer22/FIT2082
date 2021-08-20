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

// Propagator for the value_precede constraint.
// Not gonna bother to make it reified yet.
class value_precede : public propagator,
  public prop_inst<value_precede> {
   struct tag_t {
      tag_t() : p(0), q(0) { }
      tag_t(int _p, int _q) : p(_p), q(_q) { }
      unsigned short p;
      unsigned short q; 
   };

   enum Change { C_FST = 1, C_SND = 2, C_LIM = 4 }; 
   enum Status { S_Act = 1, S_Red = 2 };

   watch_result wake_fst(int xi) {
     queue_prop();
    return Wt_Keep;
   }

   watch_result wake_pre(int xi) {
     if(status & S_Red)
       return Wt_Keep;
     if(xi == fst || xi == snd) {
       queue_prop();
     }
     return Wt_Keep;
   }
   watch_result wake_cons(int xi) {
     if(status & S_Red)
      return Wt_Keep;

     if(xi < limit) {
       set(limit, xi);
       queue_prop();
     }
     return Wt_Keep;
   }

   watch_result wake_fix(int xi) {
     if(status & S_Red)
       return Wt_Keep;

     if(xi < limit && lb(xs[xi]) == cons) {
       set(limit, xi);
       queue_prop();
     }
     return Wt_Keep;
   }
  
   // x_i != t <- forall j < i, x_i != s.
   void ex_t(int xi, pval_t p, vec<clause_elt>& expl) {
     for(int ii : irange(xi)) {
       expl.push(xs[ii] == pre);
     }
   }
   
   // x_i = s <- x_j = t & forall (k in 1..j-1, k != i) (x_k != s)
   void ex_s(int tval, pval_t p, vec<clause_elt>& expl) {
     tag_t tag(cast::conv<tag_t, int>(tval));
     xs[tag.q].explain_eq(cons, expl);
     for(int ii : irange(tag.p))
       xs[ii].explain_neq(pre, expl);
     for(int ii : irange(tag.p+1, tag.q))
       xs[ii].explain_neq(pre, expl);
   }

public: 
  value_precede(solver_data* solver, int _s, int _t, vec<intvar>& _xs)
    : propagator(solver), pre(_s), cons(_t), xs(_xs),
      fst(0), snd(0), limit(xs.size()),
      status(S_Act) {
    // Find the earliest definite occurrence of lst.
    int xi = 0;
    for(; xi < xs.size(); ++xi) {
      if(is_fixed(xs[xi]) && lb(xs[xi]) == cons)
        break;
    }
    set(limit, xi);

    int ii = 0;
    for(; ii < limit; ++ii) {
      if(in_domain(xs[ii], pre))
        break;
    }
    if(ii >= limit)
      throw RootFail();
    set(fst, ii);    
    
    for(++ii; ii < limit; ++ii) {
      if(in_domain(xs[ii], pre))
        break;
    }
    if(ii >= limit) {
      // Exactly one occurrence.
      if(!set_lb(xs[fst], pre, reason()))
        throw RootFail();
      if(!set_ub(xs[fst], pre, reason()))
        throw RootFail();
      // Now redundant, so never attach.
    } else {
      set(snd, ii);

      // Now attach.
      // Limit changes
      for(int xi : irange(xs.size())) {
        xs[xi].attach(E_FIX, watch<&P::wake_fix>(xi));
        attach(s, xs[xi] != pre, watch<&P::wake_pre>(fst));
      }
      // attach(s, xs[fst] != pre, watch<&P::wake_fst>(fst));
      // fst_watched[fst] = true;

      // attach(s, xs[snd] != pre, watch<&P::wake_snd>(snd));
      // snd_watched[snd] = true;
    }
  }

  void ex_fail(int idx, vec<clause_elt>& confl) {
    for(int ii : irange(idx))
      confl.push(xs[ii] == pre);
    confl.push(xs[idx] != cons);
  }

  bool propagate(vec<clause_elt>& confl) {
    if(status & S_Red)
      return true;

    // Repair fst.
    if(!in_domain(xs[fst],pre)) {
      int f = fst;
      for(++f; f < limit; ++f) {
        if(in_domain(xs[f],pre))
          break;
      }
      if(f >= limit) {
        ex_fail(limit, confl);
        return false;
      }
      for(int ii : irange(fst, f)) {
        if(in_domain(xs[ii], cons)) {
          if(!enqueue(*s, xs[ii] != cons, expl<&P::ex_t>(ii)))
            return false;
        }
      }
      set(fst, f);
    }
    // First occurrence is a definite occurrence.
    if(is_fixed(xs[fst])) {
      set(status, (char) S_Red);
      return true;
    }
    if(snd <= fst || !in_domain(xs[snd],pre)) {
      int g = std::max((int) fst, (int) snd);
      for(++g; g < limit; ++g) {
        if(in_domain(xs[g], pre)) {
          set(snd, g);
          goto vp_supp_found;
        }
      }
      // No second support found. 
      if(!enqueue(*s, xs[fst] == pre,
        expl<&P::ex_s>(cast::conv<int, tag_t>(tag_t(fst, limit)))))
        return false;
      set(status, (char) S_Red);
    }
vp_supp_found:
    return true;
  }

  // Parameters
  int pre;
  int cons;
  vec<intvar> xs;

  // Persistent data
  Tint fst;  
  Tint snd;
  Tint limit;
  Tchar status;

  // Transient state
  char changes;
};

// Like vals-precede-chain, but just monotonically
// increasing.
// Use permutation views to deal with the rest.
class vals_precede_seq : public propagator,
  public prop_inst<vals_precede_seq> {
  enum { S_Nil = 0, S_Act = 1, S_Red = 2 };

  struct tag_t {
    tag_t(void) { }
    tag_t(unsigned int _idx, unsigned int _wit)
      : idx(_idx), wit(_wit) { }
    uint16_t idx; uint16_t wit;
  };

  watch_result wake_dis(int xi) {
    set(status, (char) S_Red);
    return Wt_Keep;
  }
  watch_result wake_act(int xi) {
    set(status, (char) S_Act);
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_lb(int xi) {
    queue_prop();
    return Wt_Keep;
  }
  watch_result wake_ub(int xi) {
    queue_prop();
    return Wt_Keep;
  }

  void ex_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    int u = xs[xi].ub_of_pval(p);
    expl.push(~r);
    for(int ii : irange(xi))
      expl.push(xs[ii] >= u);
  }

  // This requires expl_thunk::BT_PRED
  void ex_lb(int tag_int, pval_t p, vec<clause_elt>& expl) {
    tag_t t(cast::conv<tag_t, int>(tag_int));

    int l = xs[t.idx].lb_of_pval(p);
    for(int ii : irange(t.idx))
      l = std::max(l, (int) xs[ii].ub(s)+1);
    for(int ii : irange(t.idx+1, t.wit))
      l = std::max(l, (int) xs[ii].ub(s)+1);

    expl.push(~r);
    for(int ii : irange(t.idx))
      expl.push(xs[ii] >= l);
    for(int ii : irange(t.idx+1, t.wit))
      expl.push(xs[ii] >= l);
    expl.push(xs[t.wit] <= l);
  }

  void ex_r(int xi, pval_t _p, vec<clause_elt>& expl) {
    GEAS_NOT_YET;
  }

public:
  vals_precede_seq(solver_data* s, vec<intvar>& _xs, patom_t _r)
    : propagator(s), r(_r), xs(_xs), pos(xs.size()+1, 0), status(S_Nil) {
    if(lb(r)) {
      status = S_Act;
    } else {
      attach(s, r, watch<&P::wake_act>(0, Wt_IDEM));
      attach(s, ~r, watch<&P::wake_dis>(0, Wt_IDEM));
    }

    for(int xi : irange(xs.size())) {
      xs[xi].attach(E_LB, watch<&P::wake_lb>(xi, Wt_IDEM));
      xs[xi].attach(E_UB, watch<&P::wake_ub>(xi, Wt_IDEM));
    }
  }
  
  bool check(void) const { return check(s->ctx()); }
  bool check(const ctx_t& ctx) const {
    int U = 0;
    for(intvar& x : xs) {
      if(x.lb(ctx) > U)
        return false;
      if(x.ub(ctx) >= U)
        U += 1;
    }
    return true;
  }

  bool propagate(vec<clause_elt>& elt) {
#ifdef LOG_PROP
    std::cout << "[[Running values_precede]]" << std::endl;
#endif
    int U = 1;

    if(!lb(r)) {
      // Not yet active
      for(int xi : irange(xs.size())) {
        if(lb(xs[xi]) > U) {
          if(!enqueue(*s, ~r, expl<&P::ex_r>(xi)))
            return false;
          set(status, (char) S_Red);
        }
        if(ub(xs[xi]) >= U)
          U++;
      }
      return true;
    }

    // Otherwise, do propagate.
    // Run forward, updating UBs
    for(int xi : irange(xs.size())) {
      if(ub(xs[xi]) > U) {
        if(!set_ub(xs[xi], U, expl<&P::ex_ub>(xi)))
          return false;
      }
      if(ub(xs[xi]) >= U) {
        pos[U] = xi;
        U++;
      }
    }
    // Now backward, updating LBs.
    int xi = xs.size()-1;
    while(xi > 0) {
      int idx = xi;
      int L = lb(xs[idx])-1;
      for(--xi; xi > 0; --xi) {
        if(lb(xs[xi]) > L) {
          // Reset the search
          goto supp_restart;
        }
        if(ub(xs[xi]) >= L) {
          // If the latest support...
          if(pos[L] == xi) {
            // is also the earliest, update the lb.
            uint32_t tag(cast::conv<uint32_t, tag_t>(tag_t(xi, idx)));
            if(!set_lb(xs[xi], L, expl<&P::ex_lb>(tag, expl_thunk::Ex_BTPRED))) {
              return false;
            }
          }
          break;
        }
      }
supp_restart:
      continue;
    }

    return true;
  }

  void root_simplify(void) { }

  void cleanup(void) {
    is_queued = false;
  }

protected:
  patom_t r;
  vec<intvar> xs;

  vec<int> pos;

  // Persistent state
  Tchar status;
};

bool int_precede_chain(solver_data* s, vec<intvar>& xs, patom_t r = at_True) {
  return vals_precede_seq::post(s, xs, r);
}

bool int_value_precede(solver_data* s, int pre, int post, vec<intvar>& xs) {
  return value_precede::post(s, pre, post, xs);
}

}
