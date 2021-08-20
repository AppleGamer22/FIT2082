#ifndef PRED__VAR_H
#define PRED__VAR_H
// Var-like interface for predicates.
// Saves us from having to wrap preds in intvars all the time.
#include <geas/solver/solver_data.h>

namespace geas {

struct pred_var {
  typedef pval_t val_t;

  void attach(intvar_event e, watch_callback c) {
    if(e&E_LB) {
      s->pred_callbacks[p].push(c);  
    }
    if(e&E_UB) {
      s->pred_callbacks[p^1].push(c);  
    }
    if(e&E_FIX) {
      GEAS_ERROR;
    }
  }

  pval_t model_val(const model& m) const { return m.get(p); }
  pval_t lb(ctx_t& ctx) const { return pred_lb(ctx, p); }
  pval_t ub(ctx_t& ctx) const { return pred_ub(ctx, p); }
  pval_t lb(solver_data* s) const { return lb(s->state.p_vals); }
  pval_t ub(solver_data* s) const { return ub(s->state.p_vals); }

  // GKG: These are a bit ugly.
  pval_t lb_delta(ctx_t& ctx, ctx_t& old) const {
    return ctx[p] - old[p];
  }
  pval_t ub_delta(ctx_t& ctx, ctx_t& old) const {
    return ctx[p^1] - old[p^1];
  }

  pval_t lb_of_pval(pval_t p) { return p;}
  pval_t ub_of_pval(pval_t p) { return pval_inv(p); }

  patom_t operator>=(pval_t k) const { return ge_atom(p, k); }
  patom_t operator<=(pval_t k) const { return le_atom(p, k); }

  patom_t operator<(pval_t k) const { return this->operator<=(k-1); }
  patom_t operator>(pval_t k) const { return this->operator>=(k+1); }

  pid_t p;

  solver_data* s;
};

struct atom_var {
  atom_var(patom_t _at)
    : at(_at) { }

  typedef int val_t;

  int lb(const ctx_t& ctx) const { return at.lb(ctx); }
  int ub(const ctx_t& ctx) const { return at.ub(ctx); }
  int lb(const solver_data* s) const { return lb(s->ctx()); }
  int ub(const solver_data* s) const { return ub(s->ctx()); }
  int model_val(const model& m) const { return m.value(at); }

  patom_t operator>=(val_t v) const {
    if(v <= 0) return at_True;
    if(v <= 1) return at;
    return at_False;
  }
  patom_t operator<=(val_t v) const {
    if(v < 0) return at_False;
    if(v < 1) return ~at;
    return at_True;
  }
  patom_t operator>(val_t v) const { return (*this) >= v+1; }
  patom_t operator<(val_t v) const { return (*this) <= v-1; }
  patom_t operator==(val_t v) const {
    if(v == 0) return ~at;
    if(v == 1) return at;
    return at_False;
  }
  void attach(solver_data* s, intvar_event e, watch_callback c) {
    if(e&(E_LB | E_FIX)) {
      geas::attach(s, at, c);
    }
    if(e&(E_UB | E_FIX)) {
      geas::attach(s, ~at, c);
    }
  }

  // TODO: Think about boundary conditions
  int lb_of_pval(pval_t p) const {
    if(p > pval_max)
      return 2;
    return p >= at.val;
  }
  int ub_of_pval(pval_t p) const { return pval_inv(p) >= at.val; } 

  patom_t at;
};

};
#endif
