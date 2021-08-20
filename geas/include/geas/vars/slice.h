#ifndef GEAS_INT_SLICE__H
#define GEAS_INT_SLICE__H
#include <unordered_map>

#include <geas/engine/infer.h>
#include <geas/solver/model.h>
#include <geas/solver/solver_data.h>
#include <geas/vars/intvar.h>

namespace geas {

class int_slice {
  int64_t gamma(pval_t v) const {
    if(v < lb_pos)
      return lb_val;
    if(v > lb_pos + delta)
      return lb_val + delta;
    return lb_val + (v - lb_pos);
  }

  int_slice(pid_t _p, int64_t _lb, pval_t _lb_pos, pval_t _delta)
    : p(_p), lb_val(_lb), lb_pos(_lb_pos), delta(_delta) { }
public:
  int_slice(void)
    : p(0), lb_val(0), lb_pos(geas::from_int(0)), delta(0) { }

  // Should always evaluate to the same value as x.
  static int_slice from_intvar(const intvar& x) {
    ctx_t& r_ctx(x.ext->s->state.p_root);
    int64_t lb(x.lb(r_ctx));
    pval_t delta(pred_ub(r_ctx, x.p) - pred_lb(r_ctx, x.p));
    return int_slice(x.p, lb, pred_lb(r_ctx, x.p), delta);
  }

  // Inspecting
  int64_t lb(const ctx_t& ctx) const { return gamma(ctx[p]); }
  int64_t ub(const ctx_t& ctx) const { return gamma(pval_inv(ctx[p^1])); }
  
  int64_t lb_of_pval(pval_t k) const { return gamma(k); }
  int64_t ub_of_pval(pval_t k) const { return gamma(pval_inv(k)); }

  int64_t model_val(const model& m) const { return gamma(m.get(p)); }

  // Atomic constraints
  patom_t operator>=(int64_t k) const {
    if(lb_val >= k) {
      return at_True;    
    } else if(delta < (uint64_t) (k - lb_val)) {
      return at_False;
    } else {
      return patom_t(p, lb_pos + (k - lb_val));
    }
  }
  patom_t operator<=(int64_t k) const { return ~((*this) >= (k+1)); }
  patom_t operator<(int64_t k) const { return ~((*this) >= k); }
  patom_t operator>(int64_t k) const { return ((*this) >= (k+1)); }

  // Manipulating
  int_slice operator+(int64_t k) const {
    return int_slice { p, lb_val + k, lb_pos, delta };
  }
  int_slice operator-(int64_t k) const { return (*this) + (-k); }
  // Unary negation. 
  int_slice operator-(void) const {
    pid_t np(p^1);     
    int64_t nlb_val(-(lb_val + delta));
    pval_t nlb_pos(pval_inv(lb_pos+delta));
    return int_slice {np, nlb_val, nlb_pos, delta};
  }

  int_slice from(int64_t k) const {
    // Already capped above the threshold
    if(k <= lb_val)
      return *this;
    // Threshold is above the upper bound,
    // so we return a constant.
    if(k >= lb_val + (int64_t) delta)
      return int_slice { p, k, lb_pos + (k - lb_val), 0 };
    // Otherwise, increase lb_val and lb_pos, and decrease delta.
    uint64_t change(k - lb_val);
    return int_slice(p, lb_val + change, lb_pos + change, delta - change);
  }

  int_slice re_zero(int64_t k) const {
    if(k <= lb_val) {
      return int_slice(p, lb_val - k, lb_pos, delta);
    } else if(k > lb_val + (int64_t) delta) {
      // Should always return zero. Offsets probably don't matter.
      return int_slice(p, 0, lb_pos + (k - lb_val), 0);
    } else {
      // Otherwise, trim the range and reset to zero. 
      pval_t change(k - lb_val);
      return int_slice(p, 0, lb_pos + change, delta - change);
    }
  }

  // Inverse operation of lowpass.
  int_slice upto(int64_t k) const {
    if(k >= lb_val + (int64_t) delta)
      return *this;     
    if(k <= lb_val)
      return int_slice(p, k, lb_pos - (lb_val - k), 0);
    // Otherwise, lower bounds are still in place; just need to shrink delta.
    return int_slice(p, lb_val, lb_pos, k - lb_val);
  }

  void attach(solver_data* s, intvar_event e, watch_callback c) {
    if(e & E_LB)
      s->pred_callbacks[p].push(c);
    if(e & E_UB)
      s->pred_callbacks[p^1].push(c);
    if(e & E_FIX)
      GEAS_NOT_YET;
  }

  pid_t p;
  int64_t lb_val;
  pval_t lb_pos;
  pval_t delta;
};

};
#endif
