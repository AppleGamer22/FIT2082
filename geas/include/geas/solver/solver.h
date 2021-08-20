#ifndef GEAS_SOLVER__H
#define GEAS_SOLVER__H

#include <geas/engine/geas-types.h>
#include <geas/solver/expr.h>
#include <geas/solver/model.h>
#include <geas/solver/options.h>
#include <geas/vars/intvar.h>
#include <geas/vars/fpvar.h>

namespace geas {

class solver_data;

class solver {
public:
  // A model just stores the valuations
  // of atomic predicates
  enum result { SAT, UNSAT, UNKNOWN };

  solver(void);
  solver(options& opts);
  ~solver(void);

  intvar new_intvar(intvar::val_t lb, intvar::val_t ub);
  // o_intvar new_opt_intvar(intvar::val_t lb, intvar::val_t ub);

  fp::fpvar new_floatvar(fp::val_t lb, fp::val_t ub);
  patom_t new_boolvar(void);
  // Post a constraint
  // bool post(bexpr& e);
  // Assert an atom unconditionally
  bool post(patom_t p);

  // Solving
  // result solve(unsigned int conflict_limit = 0);
  bool is_consistent(void); // Check if propagation detects inconsistency
  result solve(limits l = no_limit);
  void abort(void);

  bool is_aborted(void) const;

  // Retrieve a model
  model get_model(void);

  // Incremental interface:
  // push/retract assumptions
  bool assume(patom_t p);
  bool assume(patom_t* b, patom_t* e);
  void retract(void);
  void push_assump_ctx(void);
  void pop_assump_ctx(void);
  void clear_assumptions(void);
  void get_conflict(vec<patom_t>& atom);

  // Controlling search
  void backtrack(void); // Backtrack one level
  unsigned int level(void) const; // What is the current decision level?
  void restart(void);  // Backtrack to level 0.

  void level_push(void);
  void level_pop(void);
  
  solver_data* data;  
//  intvar_manager ivar_man;
};

}

#endif
