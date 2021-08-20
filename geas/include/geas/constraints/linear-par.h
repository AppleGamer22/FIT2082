#ifndef GEAS__LINEAR_PAR__H
#define GEAS__LINEAR_PAR__H
#include <cassert>
#include <map>
#include <climits>
#include <geas/mtl/Vec.h>
#include <geas/solver/solver_data.h>
#include <geas/vars/intvar.h>

#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>

namespace geas {
// Parametric version of the incremental linear inequality
// propagator. To avoid having so much 
template<class Wt, class Var>
class lin_leq : public propagator, public prop_inst< lin_leq<Wt, Var> > {
  enum Status { S_Inactive = 0, S_Active = 1, S_Finished = 2 };
  // Internal term representation
  typedef lin_leq<Wt, Var> P;
  struct elt {
    elt(Wt _c, Var _x)
      : c(_c), x(_x) { }
    Wt c;
    Var x;
  };
  typedef trailed<Wt> WtT;
  
  forceinline Wt delta(const elt& e) const {
    return e.c * (e.x.lb(s->state.p_vals) - e.x.lb(s->wake_vals));
  }

  // As soon as slack drops below threshold, the propagator needs to activate.
  Wt compute_threshold(void) const {
    Wt t(0);
    for(const elt& e : xs) {
      t = std::max(t, e.c * (Wt) (ub(e.x) - lb(e.x)));
    }
    return t;
  }

  watch_result wake_x(int xi) {
    if(status != S_Finished) {
      Wt d(delta(xs[xi]));
      if(d > 0) {
        set(slack, slack - d);
        if(slack < threshold) {
          queue_prop();
        }
      }
    }
    return Wt_Keep;
  }

  watch_result wake_r(int _ri) {
    // Constraint is now active. Slack should be consistent,
    // but not necessarily threshold.
    if(status != S_Finished) {
      set(status, (char) S_Active);
      set(threshold, compute_threshold()); 
      if(slack < threshold) {
        queue_prop();
      }
    }
    return Wt_Keep;
  }
  
  watch_result wake_nr(int _ri) {
    set(status, (char) S_Finished);
    return Wt_Keep;
  }

  // Assuming z and x are nonnegative, find some
  // value y s.t. x * y < z. Preferably making
  // y as large as possible.
  Wt mul_inv_strict_lb(Wt z, Wt x) {
    if(std::is_integral<Wt>::value) {
      Wt y_m(z/x);
      return y_m - (x * y_m >= z);
    } else {
      return 0;
    }
  }

  // Collect a total of ex_sum from variables other than xi.
  void build_expl(int exi, Wt ex_sum, vec<clause_elt>& expl) {
    // Take into account the state at level 0. 
#if 0
    for(int xi : irange(xs.size())) {
      if(exi == xi)
        continue;
      const elt& e(xs[xi]);
      if(lb_0(e.x) < lb(e.x))
        EX_PUSH(expl, e.x < lb(e.x));
    }
    return;
#endif
    for(int xi : irange(xs.size())) {
      if(xi == exi)
        continue;
      ex_sum -= xs[xi].c * xs[xi].x.lb(s->ctx0());
    }
    // Now walk through, and collect the rest of the explanation.
    vec<int> ex_idxs;
    for(int xi : irange(xs.size())) {
      if(xi == exi)
        continue;
      // If the variable has actually changed...
      const elt& e(xs[xi]);
      if(lb_0(e.x) < lb(e.x)) {
        ex_idxs.push(xi);
        Wt d(e.c * (lb(e.x) - lb_0(e.x)));
        if(d > ex_sum) {
          ex_sum = d - ex_sum;
          goto relax_expl;
        } else {
          ex_sum -= d;
        }
      }
    }
    // Fallthrough, should never be reached.
    GEAS_ERROR;
relax_expl:
    // ex_sum must remain strictly positive.
    for(int xi : ex_idxs) {
      const elt& e(xs[xi]);
      Wt d(e.c * (lb(e.x) - lb_0(e.x)));
      if(d < ex_sum) {
        // Can discard xi entirely.
        ex_sum -= d;
        continue;
      }
      Wt dx(mul_inv_strict_lb(ex_sum, e.c));
      ex_sum -= e.c * dx;
      EX_PUSH(expl, xs[xi].x < lb(xs[xi].x) - dx);
    }
  }

  void ex_x(int xi, pval_t p, vec<clause_elt>& expl) {
    // Wt x_ub(xs[xi].x.ub_of_pval(p-1)); // This doesn't work for slices.
    Wt x_ub(xs[xi].x.ub_of_pval(p)+1); // FIXME: Only correct for integral types.
    assert(x_ub > xs[xi].x.ub_of_pval(p));
    // Need to collect values which add up to _greater than_ ex_sum.
    Wt ex_sum(k - xs[xi].c * x_ub);
    EX_PUSH(expl, ~r);
    build_expl(xi, ex_sum, expl);
  }
  void ex_r(int _ri, pval_t _p, vec<clause_elt>& expl) {
    build_expl(-1, k, expl);  
  }
      
public:
  lin_leq(solver_data* s, vec<Wt>& ks, vec<Var>& vs, Wt _k, patom_t _r = at_True)
    : propagator(s), k(_k), r(_r), slack(k), threshold(0), status(S_Inactive)  {
      for(int ii = 0; ii < vs.size(); ii++) {
        elt e = ks[ii] > 0 ? elt(ks[ii], vs[ii]) : elt(-ks[ii], -vs[ii]);
        e.x.attach(s, E_LB, this->template watch<&P::wake_x>(xs.size(), P::Wt_IDEM));
        xs.push(e);
      }
      // Initialize lower bound
      for(const elt& e : xs)
        slack.x -= e.c * lb_prev(e.x);
      // Tighten upper bound, and compute threshold? 
      if(lb(r)) {
        status.x = S_Active;
        for(elt& e : xs) {
          int x_ub = lb(e.x) + slack/e.c;
          if(x_ub < ub(e.x))
            set_ub(e.x, x_ub, reason());
          // threshold = std::max(threshold, (int) (e.c * (e.x.ub(s) - e.x.lb_prev())));
          threshold.x = std::max(threshold.x, (int) (e.c * (ub(e.x) - lb_prev(e.x))));
        }
#ifdef CHECK_STATE
        assert(slack >= k - compute_lb());
#endif
      } else {
        attach(s, r, this->template watch<&P::wake_r>(0, P::Wt_IDEM));
        attach(s, ~r, this->template watch<&P::wake_nr>(0, P::Wt_IDEM));
        for(elt& e : xs) {
          int x_ub = lb(e.x) + slack/e.c;
          if(x_ub < ub(e.x))
            add_clause(s, ~r, e.x <= x_ub);
        }
        threshold.x = 0;
      }
  }

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cout << "[[Running linear_le(slice)]]" << std::endl;
#endif
#ifdef CHECK_STATE
    assert(slack == k - compute_lb());
#endif

    if(slack < 0) {
      // Collect enough atoms to explain the sum.
      // FIXME: This is kinda weak. We really want to
      // push as much as we can onto the previous level.
      if(!enqueue(*s, ~r, this->template expl<&P::ex_r>(0, expl_thunk::Ex_BTPRED)))
        return false;
      set(status, (char) S_Finished);
      // trail_change(s->persist, status, (char) S_Red);
      return true;
#ifdef CHECK_STATE
//        assert(confl_is_current(s, confl));
#endif
    }

    if(status != S_Active || !(slack < threshold))
      return true;

    // Otherwise, propagate upper bounds.
    Wt new_threshold(0);
    for(int xi : irange(0, xs.size())) {
      elt e = xs[xi];
      Wt dx(e.c * (ub(e.x) - lb(e.x)));
      if(slack < dx) {
        // Build the explanation.
        // The ub computation _should_ be sound for real and integral types.
        // For floats, we need to make sure the rounding mode is toward -oo (or 0, since
        // everything _should_ be positive).
        if(!set_ub(e.x, lb(e.x) + (slack/e.c),
            this->template expl<&P::ex_x>(xi, expl_thunk::Ex_BTPRED)))
          return false;
      }
      new_threshold = std::max(new_threshold, (e.c * (Wt) (ub(e.x) - lb(e.x))));
    }
    if(new_threshold < slack)
      set(threshold, new_threshold);

    return true;
  }
  bool check_sat(ctx_t& ctx) {
    Wt lb(0); 
    for(const elt& e : xs)
      lb += e.c * e.x.lb(ctx);
    return !r.lb(ctx) || lb <= k;
  }

  bool check_unsat(ctx_t& ctx) {
    return !check_sat(ctx);
  }

  void cleanup(void) {
    is_queued = false;
  }

protected:
  vec<elt> xs; 
  Wt k;
  patom_t r;
  

  // What is the gap between lb(xs) and k?
  WtT slack;
  // And what is the 
  WtT threshold;

  Tchar status;
};

}
#endif
