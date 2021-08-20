#ifndef GEAS_CONFLICT__H
#define GEAS_CONFLICT__H

#include <geas/mtl/p-sparse-set.h>
#include <geas/engine/geas-types.h>
#include <geas/engine/infer-types.h>

namespace geas {

class conflict_info {
  struct phase {
    unsigned int last_seen;
    pval_t val;
  };
public:
  conflict_info(void)
    : clevel(0), confl_num(0) { }
  /*
  void new_bool(void) {
    bool_seen.push(false);
  }
  */
  void new_pred(void) {
    new_halfpred();
    new_halfpred();
    pred_saved.push({0, 0});
  }

  void new_halfpred(void) {
    pred_seen.growTo(pred_eval.size());
    pred_eval.push(0);
    // pred_assval.push(0);
    pred_hint.push(nullptr);
    // pred_saved.push({0, 0});
  }

  /*
  // Boolean fragment
  vec<bool> bool_seen;
  vec<unsigned int> bool_removed;
  */
  
  // Predicate fragment
  vec<bool> pred_is_assump;
  p_sparseset pred_seen;
  vec<pval_t> pred_eval;
  vec<pval_t> pred_assval;
  vec<watch_node*> pred_hint;
  
  vec<phase> pred_saved;

  vec<clause_elt> expl_buf;
  
  // Atoms at the current level
  int clevel;
  unsigned int confl_num;
};

// Returns the appropriate backtrack level.
int compute_learnt(solver_data* s, vec<clause_elt>& confl);
void reduce_db(solver_data* s);

bool confl_is_current(solver_data* s, vec<clause_elt>& confl);

// Retrieve the last conflict, resolved back to assumptions
void retrieve_assumption_nogood(solver_data* s, vec<patom_t>& confl);

// Debugging
bool check_inference(solver_data* s, propagator* p, patom_t z, vec<clause_elt>& expl);
bool check_confl(solver_data* s, propagator* p, vec<clause_elt>& expl);
}

#endif
