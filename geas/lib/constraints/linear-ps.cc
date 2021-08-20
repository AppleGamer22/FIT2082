#include <cassert>
#include <map>
#include <geas/mtl/Vec.h>
#include <geas/solver/solver_data.h>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/vars/intvar.h>

#define SKIP_L0
namespace geas {

struct elt {
  typedef typename intvar::val_t val_t;

  int c;
  intvar x;

  inline bool is_fixed(ctx_t& ctx) const { return x.is_fixed(ctx); }
  inline val_t lb(ctx_t& ctx) const { return c * x.lb(ctx); }
  inline val_t ub(ctx_t& ctx) const { return c * x.ub(ctx); }
};

// Linear le propagator with partial sums.
class lin_le_ps : public propagator, public prop_inst<lin_le_ps> {
  enum { Var_None = -1 };
  enum { S_Active = 1, S_Red = 2 };

  enum { C_NONE = 0, C_SLACK = 1, C_FIX = 2 };

  // c and lb(x) are both nonnegative.
  forceinline int delta(int c, pid_t p) {
    return c * (s->state.p_vals[p] - s->wake_vals[p]);
  }

  int compute_lb(void) {
    int l = fix_sum;
    for(int xi : irange(fix_var, xs.size()))
      l += lb(xs[xi]);
    return l;
  }

  int compute_threshold(void) {
    int r = 0;

    for(int xi : irange(fix_var, xs.size())) {
      const elt& e(xs[xi]);
      int diff = ub(e.x) - lb(e.x);
      r = std::max(r, e.c * diff);
    }
    return r;
  }

  watch_result wake_r(int xi) {
    // Force the threshold to be
    // recomputed
    change |= C_SLACK;
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_x_fix(int xi) {
    if(fix_var < xi) {
      fix_watched[xi] = false;
      return Wt_Drop;
    }
    if(status&S_Red)
      return Wt_Keep;

    assert(xi == fix_var);
    change |= C_FIX;
    queue_prop(); 
    return Wt_Keep; 
  }

  watch_result wake_x(int xi) {
    if(status&S_Red)
      return Wt_Keep;

    set(slack, slack - delta(xs[xi].c, xs[xi].x.p));

    if(slack < threshold) {
      change |= C_SLACK;
      queue_prop();
    }
    return Wt_Keep;
  }
  
  template<class E>
  void make_expl(int var, int x0, int slack, E& ex) {
    assert(slack >= 0);

    vec<int> xs_pending;
    // First, collect things we can omit entirely, or
    // include at the previous decision level
    for(int xi : irange(x0, xs.size())) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb(s);
#ifndef SKIP_L0
        int x_lb_0 = lb_0(e.x);
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
#endif
        int x_lb_p = lb_prev(e.x);
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x < x_lb_p); 
          continue;
        }
        xs_pending.push(xi);
    }

    // Then, add things at the current level
    assert(slack >= 0);
    for(int xi : xs_pending) {
      elt e = xs[xi];
      int diff = slack/e.c;
      ex.push(e.x < e.x.lb(s) - diff);
      slack -= e.c * diff;
      assert(slack >= 0);
    }
  }

  void ex_r(int ex_slack, pval_t p, vec<clause_elt>& expl) {
    // Find the appropriate ps-var
    int pi = fix_var;
    // Collect the upper-bounds of other vars
    // Simple explanation: no generalization for now.
    int sum_lb = 0;
    int ex_val = k+1;

    for(int xi = pi; xi < xs.size(); xi++) {
      sum_lb += lb(xs[xi]); 
    }
    if(sum_lb < ex_val) {
      while(pi > 0) {
        pval_t fval = pred_lb_prev(s, ps[pi-1]);
        if(ex_val <= fval + sum_lb) {
          // assert(fval > 0); // Otherwise, we've already stopped.
          if(fval > 0) {
            expl.push(le_atom(ps[pi-1], fval-1));
            ex_val -= fval;
            //expl.push(le_atom(ps[pi-1], ex_val - sum_lb));
            //ex_val = sum_lb;
          }
          break;
        }
        pi--;
        sum_lb += lb(xs[pi]);
      }
    }
    make_expl(xs.size(), pi, sum_lb - ex_val, expl);
  }
  
  void ex_x(int xj, pval_t p, vec<clause_elt>& expl) {
    // Collect the upper-bounds of other vars
    // Simple explanation: no generalization for now.
    expl.push(~r);

    int xj_ub = xs[xj].x.ub_of_pval(p);
    int ex_val = k - xs[xj].c*(xj_ub+1) + 1;

    // Find the appropriate ps-var
    int pi = std::min(xj, (int) fix_var);
    int sum_lb = 0;

    for(int xi = pi; xi < xs.size(); xi++) {
      if(xi == xj)
        continue;
      sum_lb += lb(xs[xi]); 
    }
    if(sum_lb < ex_val) {
      while(pi > 0) {
        pval_t fval = pred_lb_prev(s, ps[pi-1]);
        if(ex_val <= fval + sum_lb) {
          // assert(fval > 0); // Otherwise, we've already stopped.
          if(fval > 0) {
            expl.push(le_atom(ps[pi-1], fval-1));
            ex_val -= fval;
          }
          break;
        }
        pi--;
        sum_lb += lb(xs[pi]);
      }
    }
    make_expl(xj, pi, sum_lb - ex_val, expl);
  }

  void ex_ps(int xi, pval_t p, vec<clause_elt>& expl) {
    const elt& e = xs[xi];
    if(e.c * lb(e.x) >= p) {
      expl.push(e.x < iceil(p, e.c));
      return;
    }
    assert(xi > 0);
#if 0
    pval_t ep = std::min(p, pred_lb(s, ps[xi-1]));
    expl.push(le_atom(ps[xi-1], ep-1));
    expl.push(e.x < iceil(p - ep, e.c));
#else
    expl.push(e.x < lb(e.x));
    expl.push(le_atom(ps[xi-1], p - (e.c * lb(e.x)) - 1));
#endif
  }

  public: 

    // WARNING: Elts should be normalized first.
    lin_le_ps(solver_data* s, patom_t _r, vec<elt>& _xs, int _k)
      : propagator(s), r(_r), xs(_xs), k(_k),
        fix_var(0), fix_sum(0),
        slack(0), threshold(0),
        status(0), change(0) {
      // Allocate the partial-sum literals.
      assert(k >= 0);

      int ps_ub = 0;
      int init_thresh = 0;
      for(int ii : irange(xs.size())) {
        xs[ii].x.attach(E_LB, watch<&P::wake_x>(ii, Wt_IDEM));
        int u = ub(xs[ii]);
        ps_ub = std::min(k+1, ps_ub + u);
        init_thresh = std::max(init_thresh, u);
        ps.push(new_pred(*s, 0, ps_ub, PR_NOBRANCH));
        fix_watched.push(false);
      }
      xs[0].x.attach(E_FIX, watch<&P::wake_x_fix>(0, Wt_IDEM));
      fix_watched[0] = true;

      slack.x = k;
      if(s->state.is_entailed(r)) {
        threshold.x = init_thresh;
      }
    }

    void root_simplify(void) {
     
    }
    
    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le(ps)]]" << std::endl;
#endif
      if(status&S_Red)
        return true;
      
      if(change&C_SLACK) {
        if(slack < 0) {
          if(!enqueue(*s, ~r, ex_thunk(ex<&P::ex_r>, 0, expl_thunk::Ex_BTPRED)))
            return false;
          set(status, (char) S_Red);
          return true;
        }
        assert(s->state.is_entailed(r));
        // Otherwise, scan the un-fixed variables to update domains
        // and find the new threshold.
        int new_threshold = 0;
        for(int xi : irange(fix_var, xs.size())) {
          elt e = xs[xi];
          int x_diff = slack/e.c;
          int x_ub = e.x.lb(s) + x_diff;
          if(x_ub < e.x.ub(s)) {
            // Build the explanation
            if(!set_ub(e.x, x_ub,
                ex_thunk(ex<&P::ex_x>, xi, expl_thunk::Ex_BTPRED)))
              return false;
          }
          new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub(s) - e.x.lb(s))));
        }
        set(threshold, new_threshold);
      }

      // Update fixed variables
      if(change&C_FIX) {
        assert(is_fixed(xs[fix_var].x));
        int fs = fix_sum;
        int fi = fix_var;

        do {
          assert(fs >= 0);
          fs += lb(xs[fi]);
          assert(fs <= k); // Otherwise, we should have slack < 0.
          if(!enqueue(*s, ge_atom(ps[fi], fs),
              ex_thunk(ex<&P::ex_ps>, fi, expl_thunk::Ex_BTPRED)))
            return false;
          ++fi;
        } while(fi < xs.size() && is_fixed(xs[fi].x));

        set(fix_sum, fs);
        set(fix_var, fi);

        // Wake up when the next variable in order is fixed.
        if(fi < xs.size() && !fix_watched[fi]) {
          xs[fi].x.attach(E_FIX, watch<&P::wake_x_fix>(fi, Wt_IDEM));
          fix_watched[fi] = true;
        }
      }
      return true;
    }

    void cleanup(void) {
      is_queued = false;
      change = C_NONE;
    }

    patom_t r;
    vec<elt> xs;
    int k;

    // Partial sum tracking
    vec<pid_t> ps;
    // Which variables are watched on E_FIX?
    vec<bool> fix_watched;
    Tint fix_var;
    Tint fix_sum;

    // Persistent state
    Tint slack;
    Tint threshold;
    Tchar status;

    // Transient state
    unsigned char change;
};

bool linear_le_ps(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r) {
  // Normalize the (c, x) pairs.
  int sum_ub = 0;
  vec<elt> xs;
  const ctx_t& ctx(s->state.p_last);

  for(int ii : irange(vs.size())) {
    int c = ks[ii];
    intvar x = vs[ii];

    if(c == 0)
      continue;
    if(c < 0) {
      c = -c; x = -x;
    }
    if(x.is_fixed(s)) {
      k -= c * x.lb(s);
      continue; 
    }
    if(x.lb(ctx) != 0) {
      k -= c * x.lb(ctx);
      x -= x.lb(ctx);
    }
    assert(c > 0 && x.lb(s) >= 0);
    xs.push(elt { c, x });
  }
  // Now eliminate any variables whose
  // coefficients are sufficiently large.
  int jj = 0;
  for(int ii : irange(xs.size())) {
    elt e(xs[ii]);
    if(e.c > k) {
      if(!add_clause(s, ~r, e.x <= 0))
        return false;
    } else {
      sum_ub += e.c * e.x.ub(s);
      xs[jj++] = e;
    }
  }
  xs.shrink_(xs.size() - jj);
  
  if(k < 0) {
    // Infeasible; set ~r.
    return enqueue(*s, ~r, reason());
  } else if(k == 0) {
    // r forces every var to take its lb.
    assert(xs.size() == 0);
    /*
    for(const elt& e : xs) {
      if(!add_clause(s, ~r, e.x <= 0))
        return false;
    }
    */
  } else if(k < sum_ub) {
    // _Might_ be violated; make a propagator
    // new lin_le_ps(s, r, xs, k);
    return lin_le_ps::post(s, r, xs, k);
  }
  return true;
}

}
