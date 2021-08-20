#ifndef GEAS_SUM__H
#define GEAS_SUM__H
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>

namespace geas {

// Parametric version of the sum(xs) <= k constraint, so we can
// just swap in other variable types.
template<typename V>
struct int_sum {
  class leq : public propagator, public prop_inst<leq> {
  enum Status { S_Wait = 0, S_Active = 1, S_Red = 2 };
  enum { Var_None = -1 };

  typedef prop_inst<leq> I;
  typedef leq P;
  
  void update_binding(void) {
    int gap = k - sum_lb;
    int max_window = 0;
    bool saved = 0;
    for(int xi : irange(binding.size(), xs.size())) {
      if(lb(xs[xi]) + gap < ub(xs[xi])) {
        if(!saved) {
          trail_push(s->persist, binding.sz);
          saved = true;
        }
        binding.insert(xi);
      } else {
        max_window = std::max(max_window, (int) (ub(xs[xi]) - lb(xs[xi])));
      }
    }
    set(threshold, k - max_window);
  }

  watch_result wake_x(int xi) {
    if(!(status&S_Red)) {
      set(sum_lb, (int) (sum_lb + lb_delta(xs[xi])));
      if(sum_lb > threshold) {
        if(status&S_Active) {
          update_binding();
          if(binding.size() > 0)
            queue_prop();
        } else {
          queue_prop();
        }
      }
    }
    return Wt_Keep;
  }

  watch_result wake_r(int _xi) {
    if(!(status&S_Red)) {
      // Compute new threshold   
      set(status, (char) S_Active);
      update_binding();
      if(binding.size() > 0)
        queue_prop();
    }
    return Wt_Keep;
  }
  watch_result wake_deact(int _xi) {
    set(status, (char) S_Red);
    return Wt_Keep;
  }

  // FIXME
  void make_expl(int xi, int lim, vec<clause_elt>& expl) {
#if 0
    for(int ii : irange(xs.size())) {
      if(ii == xi)
        continue;  
      expl.push(xs[ii] < lb(xs[ii]));
    }
#else
    // How much 'value' do we have available?
    int avail = 0;
    for(int ii : irange(xs.size())) {
      if(ii == xi) continue;
      avail += lb(xs[ii]);
    }
    int slack = avail - lim;
    assert(slack >= 0);
    
    vec<int> pending;
    for(int ii : irange(xs.size())) {
      if(ii == xi) continue;
      const V& x(xs[ii]);
      int x_lb = lb(x);
      int x_lb0 = lb_0(x);
      if(x_lb - x_lb0 <= slack) {
        slack -= (x_lb - x_lb0);
        continue; 
      }
      int x_lb_p = lb_prev(x);
      if(x_lb - x_lb_p <= slack) {
        slack -= (x_lb - x_lb_p);
        assert(slack >= 0);
        expl.push(x < x_lb_p);
        continue;
      }
      pending.push(ii);
    }
    if(pending.size() > 0) {
      assert(slack >= 0);
      const V& x0(xs[pending[0]]);
      expl.push(x0 < lb(x0) - slack);
      for(int ii : irange(1, pending.size())) {
        expl.push(xs[pending[ii]] < lb(xs[pending[ii]]));
      }
    }
#endif
  }

  void ex_r(int _xi, pval_t _p, vec<clause_elt>& expl) {
    // Need to explain why the sum is at least k+1. 
    make_expl(Var_None, k+1, expl);
  }

  void ex_x(int xi, pval_t p, vec<clause_elt>& expl) {
    int x_ub = xs[xi].ub_of_pval(p);

    int lim = k - x_ub;

    expl.push(~r);
    make_expl(xi, lim, expl);
  }

public:  
  leq(solver_data* s, vec<V>& _xs, int _k, patom_t _r)
    : propagator(s), xs(_xs), k(_k), r(_r), binding(xs.size())
    , sum_lb(0), threshold(k), status(S_Wait) {
    // Initialize everything
    ctx_t& ctx(s->state.p_last);
    int init_lb = 0;
    int init_ub = 0;
    for(const V& x : xs) {
      init_lb += x.lb(ctx);
      init_ub += x.ub(ctx);
    }
    
    set(sum_lb, init_lb);
    if(init_lb > k) {
      // sum(xs) already above k.
      if(!enqueue(*s, ~r, reason()))
        throw RootFail();
    } else if(k < init_ub) {
      for(int xi: irange(xs.size())) {
        xs[xi].attach(E_LB, this->template watch<&P::wake_x>(xi, I::Wt_IDEM));
      }
      if(lb(r)) {
        // Already enforced; tighten bounds.
        set(status, (char) S_Active);
        update_binding();
        int slack = k - init_lb;
        for(int xi : binding) {
          const V& x(xs[xi]);
          int x_ub = x.lb(ctx) + slack; 
          if(x_ub < ub(x)) {
            if(!set_ub(x, x_ub, reason()))
              throw RootFail();
          }
        }
      } else {
        // Not yet active
        set(threshold, k);
        attach(s, r, this->template watch<&P::wake_r>(0, I::Wt_IDEM));
        attach(s, ~r, this->template watch<&P::wake_deact>(0, I::Wt_IDEM));
      }
    }
  }

  bool propagate(vec<clause_elt>& confl) {
    if(sum_lb > k) {
      if(!enqueue(*s, ~r, this->template expl<&P::ex_r>(0, expl_thunk::Ex_BTPRED)))
        return false;
      set(status, (char) S_Red);
      return true;
    }
    
    if(status&S_Active) {
      int gap = k - sum_lb;
      for(int xi : binding) {
        int x_ub = lb(xs[xi]) + gap;
        if(x_ub < ub(xs[xi])) {
          if(!enqueue(*s, xs[xi] <= x_ub,
            this->template expl<&P::ex_x>(xi, expl_thunk::Ex_BTPRED)))
            return false;
        }
      }
    }
    return true;
  }

  vec<V> xs;
  int k;
  patom_t r;

  p_sparseset binding;
  Tint sum_lb;
  Tint threshold;

  Tchar status;
};

};

};
#endif
