#ifndef GEAS_STATE__H
#define GEAS_STATE__H
#include <geas/engine/geas-types.h>
#include <geas/mtl/Vec.h>

namespace geas {

// Interpreting a pair of pvals as a range.
// Keeping persistent pvar_refs is probably risky,
// if new predicates are liable to be added.
/*
class pvar_ref {
public: 
  pvar_ref(pval_t* _b) : base(_b) { }

  uint64_t lb(void) const { return base[0]; }  
  uint64_t ub(void) const { return pval_max - base[1]; }

  // Deal with trailing
  bool set_lb(uint64_t lb) {
    base[0] = lb;
    return lb <= pval_max - base[1];
  }
  bool set_ub(uint64_t ub) {
    base[1] = pval_max - ub;
    return base[0] <= ub;
  }
  pval_t* base;     
};
*/

// Representing the current state of atomic predicates
class pred_state {
public:
  pred_state(void) {
      // solver_data constructor will call new_pred 
  }

  // As with infer, preds are added in pairs.
  pid_t new_pred(pval_t lb, pval_t ub) {
    pval_t uval = pval_inv(ub);

    pid_t p = p_vals.size();
    p_vals.push(lb);
    p_vals.push(uval);

    p_last.push(lb);
    p_last.push(uval);

    p_root.push(lb);
    p_root.push(uval);

    // initializers.push();

    return p;
  }

  // bool pred_is_bool(pid_t pid) const { return pid <= 1; }
  // bool pred_is_bool(pid_t pid) const { return false; }

  forceinline
  bool is_entailed(patom_t atom) const {
    return atom.val <= p_vals[atom.pid];
  }
  forceinline
  bool is_inconsistent(patom_t atom) const {
    // return pval_max - p_vals[atom.pid^1] < atom.val;
    return p_vals[atom.pid^1] >= pval_contra(atom.val);
    // return is_entailed(~atom);
  }

  forceinline
  bool is_entailed_l0(patom_t atom) const {
    return atom.val <= p_root[atom.pid];
  }
  forceinline
  bool is_inconsistent_l0(patom_t atom) const {
    // return pval_max - p_root[atom.pid^1] < atom.val;
    return is_entailed_l0(~atom);
  }

  forceinline bool is_inconsistent_prev(patom_t atom) const {
    // return pval_max - p_root[atom.pid^1] < atom.val;
    return pval_max - p_last[atom.pid^1] < atom.val;
  }

/*
  pvar_ref get_ref(pid_t pi) {
    assert(!(pi&1)); // pi must be the base.
    return pvar_ref(&p_vals[pi]);
  }
  */

  bool post(patom_t atom) {
    if(is_inconsistent(atom))
      return false;
    
    if(!is_entailed(atom))
      p_vals[atom.pid] = atom.val; 
    return true;
  }
  
  // vec<char> b_assigns;
  vec<pval_t> p_vals; // Current values of predicates
  vec<pval_t> p_last; // Values at previous decision level
  vec<pval_t> p_root; // ...and at the root

};

void log_state(pred_state& s);

}

#endif
