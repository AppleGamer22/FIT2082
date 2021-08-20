#include <geas/vars/fpvar.h>

namespace geas {
namespace fp {

// Creating and accessing the manager
void* create_fp_man(solver_data* s) { return new manager(s);  }
void destroy_fp_man(void* ptr) { delete static_cast<manager*>(ptr); }

static man_id_t fpman_id = register_manager(create_fp_man, destroy_fp_man);

manager* get_man(solver_data* s) { return static_cast<manager*>(s->managers[fpman_id].ptr); }

manager::manager(solver_data* _s)
  : s(_s) {
    
}

fval fpvar::model_val(const model& m) const {
  return cast::to_float(m.get(p));   
}

void fpvar::attach(event e, watch_callback c) {
  // man->attach(idx, e, c);
  if(e&E_LB) {
    ext->b_callbacks[p&1].push(c);  
  }
  if(e&E_UB) {
    ext->b_callbacks[(p&1)^1].push(c);
  }
  if(e&E_FIX) {
    ext->fix_callbacks.push(c);
  }
}

static watch_result wakeup(void* ptr, int idx) {
  // This is a bit ugly
  fpvar_ext* ext = static_cast<fpvar_ext*>(ptr);
  void* origin = ext->s->active_prop;
  // Do some stuff
  if(pred_fixed(ext->s, ext->p)) {
    run_watches(ext->fix_callbacks, origin);
  }
  run_watches(ext->b_callbacks[idx], origin);

  return Wt_Keep;
}

fpvar manager::new_var(float lb, float ub) {
  pid_t p = new_pred(*s, cast::from_float(lb), cast::from_float(ub));
  fpvar_ext* ext = new fpvar_ext(s, p);
  s->pred_callbacks[p].push(watch_callback(wakeup, ext, 0));
  s->pred_callbacks[p+1].push(watch_callback(wakeup, ext, 1));

  return fpvar { p, ext };
}

}
}
