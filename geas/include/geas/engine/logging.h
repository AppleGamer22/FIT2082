#ifndef GEAS_PROOF_LOG_H
#define GEAS_PROOF_LOG_H
#include <geas/engine/geas-types.h>
#include <geas/engine/infer-types.h>

#include <geas/mtl/Vec.h>


namespace geas {

class solver_data;

struct proof_log {
  int scope_constraint;  // What id do we give posted constraints?
  int active_constraint; // Source of any current inferences
  int last_hint;   // Active hint in the logfile
  int next_inf_id; // Next free inference id

  FILE* log_file;

  vec<int> deriv;
  vec<int> temp;
};

namespace log {

// void start_derivation(proof_log& l);
void start_infer(solver_data& l);
void add_atom(solver_data& l, patom_t at);
void finish_infer(solver_data& l);
void log_learnt(solver_data& l, vec<clause_elt>& learnt);
void log_deletion(solver_data& l, clause* cl);

}

}

#endif
