#ifndef GEAS_FPVAR_H
#define GEAS_FPVAR_H
#include <geas/solver/solver_data.h>
#include <geas/utils/cast.h>

namespace geas {
namespace fp {

typedef float fval;
typedef fval val_t;

enum event { E_None = 0, E_LB = 1, E_UB = 2, E_LU = 3, E_FIX = 4 };

struct fpvar_ext {
  fpvar_ext(solver_data* _s, pid_t _p)
    : s(_s), p(_p) { }

  vec<watch_callback> b_callbacks[2];
  vec<watch_callback> fix_callbacks;
  solver_data* s; 
  pid_t p;
};

struct fpvar {
  typedef fval val_t;
  inline fval lb(ctx_t& ctx) const {
    return cast::to_float(ctx[p]);
  }
  inline fval ub(ctx_t& ctx) const {
    return cast::to_float(pval_inv(ctx[p^1]));
  }
  inline fval lb(solver_data* s) const { return lb(s->state.p_vals); }
  inline fval ub(solver_data* s) const { return ub(s->state.p_vals); }
  inline fval lb_0(solver_data* s) const { return lb(s->state.p_root); }
  inline fval ub_0(solver_data* s) const { return ub(s->state.p_root); }
  inline fval lb_prev(solver_data* s) const { return lb(s->state.p_last); }
  inline fval ub_prev(solver_data* s) const { return ub(s->state.p_last); }
  
  /*
  bool set_lb(fval min, reason r);
  bool set_ub(fval max, reason r);
  */

  void attach(event e, watch_callback c);
  fval model_val(const model& m) const;

  patom_t operator>=(fval v) {
    return patom_t(p, cast::from_float(v));
  }
  patom_t operator>(fval v) {
    return patom_t(p, cast::from_float(v)+1);
  }
  patom_t operator<=(fval v) {
    return ~patom_t(p, cast::from_float(v)+1);
  }
  patom_t operator<(fval v) {
    return ~patom_t(p, cast::from_float(v));
  }
  /*
  patom_t operator==(fval v);
  patom_t operator!=(fval v);
  */
  pid_t p;
  fpvar_ext* ext;
};

class manager {
public:
  manager(solver_data* _s);
  fpvar new_var(fval lb, fval ub);

//  void attach(unsigned int vid, event e, watch_callback c);

  vec<pid_t> var_preds;
  vec<fpvar_ext*> exts;

  solver_data* s;
};

manager* get_man(solver_data* s);
fpvar new_var(solver_data* s, float lb, float ub);

}
}

#endif
