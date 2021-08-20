#ifndef GEAS_BRANCH_H
#define GEAS_BRANCH_H
#include <geas/engine/geas-types.h>
#include <geas/engine/infer.h>

namespace geas {

class brancher {
public:
  virtual ~brancher(void) { }
  virtual patom_t branch(solver_data* s) = 0;
  virtual bool is_fixed(solver_data* s) = 0;
};

// Standard branchers
enum VarChoice { Var_InputOrder, Var_FirstFail, Var_Smallest, Var_Largest };
enum ValChoice { Val_Min, Val_Max, Val_Split, Val_Saved, Val_Pol, Val_Default };

brancher* default_brancher(solver_data* s);
brancher* pred_act_branch(solver_data* s);
brancher* atom_act_branch(solver_data* s);

brancher* basic_brancher(VarChoice var_choice, ValChoice val_choice, vec<pid_t>& preds);
brancher* seq_brancher(vec<brancher*>& branchers);
brancher* limit_brancher(brancher* b);
brancher* warmstart_brancher(vec<patom_t>& decs);
brancher* toggle_brancher(vec<brancher*>& bs);

// brancher* priority_brancher(VarChoice choice, vec<intvar>& sel, vec<brancher*>& br);
  
patom_t branch(solver_data* s);

}
#endif
