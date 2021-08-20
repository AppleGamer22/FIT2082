#include <geas/mtl/Heap.h>
#include <geas/solver/solver_data.h>
#include <geas/solver/branch.h>

namespace geas {

class simple_branch : public brancher {
public:
  simple_branch(void) { }
   
  bool is_fixed(solver_data* s) {
    for(pid_t pi = 0; pi < s->state.p_vals.size(); pi+=2) {
      if(!pred_fixed(s, pi))
        return false;
    }
    return true;
  }
  patom_t branch(solver_data* s) {
    for(pid_t pi = 0; pi < s->state.p_vals.size(); pi+=2) {
      pval_t lb = s->state.p_vals[pi];
      pval_t ub = pval_max - s->state.p_vals[pi+1];
      if(lb < ub) {
        return patom_t(pi, lb + (1 + ub - lb)/2);
      }
    }
    
    return at_Undef;
  }
};

static forceinline pval_t lb(solver_data* s, pid_t pi) {
  return s->state.p_vals[pi];
}
static forceinline pval_t ub(solver_data* s, pid_t pi) {
  return pval_max - s->state.p_vals[pi^1];
}

template<int ValC>
struct branch_val {
  static forceinline patom_t branch(solver_data* s, pid_t p) {
    switch(ValC) {
      case Val_Min:
        return ~patom_t(p, lb(s, p)+1);
      case Val_Max:
        return patom_t(p, ub(s, p));
      case Val_Split:
        {
          // pval_t mid = lb(s, p) + ((ub(s, p) - lb(s, p) + 1)/2);
          // return patom_t(p, mid);
          pval_t mid = lb(s, p) + ((ub(s, p) - lb(s, p))/2);
          return le_atom(p, mid);
        }
      case Val_Pol:
        {
          if(s->polarity[p>>1].branch^(p&1)) {
            return ge_atom(p, ub(s, p));
          } else {
            return le_atom(p, lb(s, p));
          }
        }
      case Val_Saved:
        {
          // pval_t saved = s->confl.pred_saved[p].val;
#if 1
          pval_t saved = p&1 ? pval_inv(s->confl.pred_saved[p>>1].val)
                             : s->confl.pred_saved[p>>1].val;
          if(saved <= lb(s, p))
            // return ~patom_t(p, lb(s, p)+1);
            return le_atom(p, lb(s, p));
          if(ub(s, p) <= saved)
            // return patom_t(p, ub(s, p));
            return ge_atom(p, ub(s, p));
          // return patom_t(p, saved);
          // return ge_atom(p, saved);
          // return le_atom(p, saved);
          return (s->polarity[p>>1].branch^(p&1)) ? ge_atom(p, saved) : le_atom(p, saved);
#else
          p = p&~1;
          return s->confl.pred_saved[p>>1].val&1 ? le_atom(p, lb(s, p)) : ge_atom(p, ub(s, p));
          // return s->confl.pred_saved[p>>1].val&1 ? ge_atom(p, ub(s, p)) : le_atom(p, lb(s, p));
#endif
        }
      default:
        GEAS_NOT_YET; 
        return at_Error;
    }
  }
};

class prog_branch : public evt< prog_branch > {
public:
  void on_pred(void) {
//    fprintf(stderr, "Called on_pred\n");
    step.push(1); 
  }

  static void branch_call(void* ptr) {
    return static_cast<prog_branch*>(ptr)->on_branch();
  }
  static void pred_call(void* ptr) {
    return static_cast<prog_branch*>(ptr)->on_pred();
  }

  void on_branch(void) {
    trail_fake(s->persist, step[last], std::max(step[last], step[last]<<1));
    if(step[last] > 1)
      step[last] = step[last]>>1;
  }

  prog_branch(solver_data* _s)
    : s(_s) {
//    fprintf(stderr, "Created (%d)!\n", s->state.p_vals.size());
    for(int pi = 0; pi < s->state.p_vals.size(); pi++)
      step.push(1);
    s->on_pred.push(event_callback(pred_call, this));
    s->on_branch.push(event_callback(branch_call, this));
  }

  // FIXME: Boundary conditions
  patom_t branch(solver_data* s, pid_t p) {
    int idx = p>>1;
    last = idx;
//    fprintf(stderr, "%d/%d\n", idx, step.size());
    while(step.size() <= idx)
      step.push(1);
    assert(idx < step.size());
    /*
    switch(ValC) {
      case Val_Min:
      */
      {
        pval_t diff = std::min(ub(s, p) - lb(s, p) - 1, step[idx]);
        return le_atom(p, lb(s, p)+diff);
      }
      /*
      case Val_Max:
      {
        bound = std::max(ub(s, p)-step[p], lb(s, p)+1);
        pval_t diff = std::min(ub(s, p) - lb(s, p) - 1, step[idx]);
        return ge_atom(p, ub(s, p)-diff);
      }
      default:
        GEAS_NOT_YET; 
        return at_Error;
    }
    */
  }

  solver_data* s;

  vec<pval_t> step;
  pid_t last;
};


template<int ValC>
class inorder_branch : public brancher {
public:
  inorder_branch(vec<pid_t>& _preds)
    : vars(_preds), start(0) { }

  bool is_fixed(solver_data* s) {
    pid_t* p = vars.begin() + start;
    pid_t* end = vars.end();

    if(p != end) {
      if(!pred_fixed(s, *p))
        return false;
      for(++p; p != end; ++p) {
        if(!pred_fixed(s, *p)) {
          start.set(s->persist, p - vars.begin());
          return false;
        }
      }
      start.set(s->persist, p - vars.begin());
    }
    return true;
  }

  patom_t branch(solver_data* s) {
    pid_t* p = vars.begin() + start;
    pid_t* end = vars.end();

    if(p == end)
      return at_Undef;
    
    if(lb(s, *p) != ub(s, *p))
      return branch_val<ValC>::branch(s, *p);

    patom_t at = at_Undef;
    for(++p; p != end; ++p) {
      if(lb(s, *p) != ub(s, *p)) {
        // Branch found
        at = branch_val<ValC>::branch(s, *p);  
        break;
      }
    }
    start.set(s->persist, p - vars.begin());
    return at;
  }
  
  vec<pid_t> vars;
  Tint start;
};

template<int VarC>
forceinline pval_t score(solver_data* s, pid_t p) {
    switch(VarC) {
      case Var_Smallest:
        return lb(s, p);
      case Var_Largest:
        return pval_max - ub(s, p);
      case Var_FirstFail:
        return ub(s, p) - lb(s, p); 
      default:
        return 0;
  }
}

template<int VarC, int ValC>
class basic_branch : public brancher {
public:
  basic_branch(vec<pid_t>& _preds)
    : vars(_preds), start(0) { }

  bool is_fixed(solver_data* s) {
    pid_t* p = vars.begin() + start;
    pid_t* end = vars.end();  

    if(p != end) {
      if(!pred_fixed(s, *p))
        return false;

      for(++p; p != end; ++p) {
        if(!pred_fixed(s, *p)) {
          start.set(s->persist, p - vars.begin());
          return false;
        }
      }
      start.set(s->persist, vars.size());
    }
    return true;
  }

  patom_t branch(solver_data* s) {
    pid_t* end = vars.end();

    pid_t* choice = end;
    pval_t choice_score = pval_err;
     
    pid_t* p = vars.begin() + start;
    for(; p != end; ++p) {
      if(lb(s, *p) == ub(s, *p))
        continue;
      pval_t p_score = score<VarC>(s, *p);
      if(p_score < choice_score) {
        choice = p;
        choice_score = p_score;
      }
    }

    if(choice == end)
      return at_Undef;

    return branch_val<ValC>::branch(s, *choice);
  }

  vec<pid_t> vars;
  Tint start;
};

class seq_branch : public brancher {
public:
  seq_branch(vec<brancher*>& _bs)
    : branchers(_bs), start(0) { }

  bool is_fixed(solver_data* s) {
    brancher** end = branchers.end();
    brancher** b = branchers.begin() + start;

    if(b != end) {
      if(!(*b)->is_fixed(s))
        return false;
      for(++b; b != end; ++b) {
        if(!(*b)->is_fixed(s)) {
          start.set(s->persist, b - branchers.begin());
          return false;
        }
      }
      start.set(s->persist, branchers.size());
    }
    return true;
  }

  patom_t branch(solver_data* s) {
#ifndef NDEBUG
    for(brancher* b : range(branchers.begin(), branchers.begin()+start))
      assert(b->is_fixed(s));
#endif
    brancher** end = branchers.end();
    brancher** b = branchers.begin() + start;

    if(b == end)
      return at_Undef;
    
    patom_t at = (*b)->branch(s); 
    if(at != at_Undef)
      return at;

    for(++b; b != end; ++b) {
      at = (*b)->branch(s);
      if(at != at_Undef) {
        break; 
      }
    }
    
    start.set(s->persist, b - branchers.begin());
    return at;
  }

  vec<brancher*> branchers;
  Tint start;
};

brancher* seq_brancher(vec<brancher*>& bs) {
  return new seq_branch(bs); 
}

class limit_branch : public brancher {
public:
  limit_branch(brancher* _b)
    : b(_b) { }

  bool is_fixed(solver_data* s) {
    return s->stats.restarts || b->is_fixed(s);
  }

  patom_t branch(solver_data* s) {
    if(s->stats.restarts == 0)
      return b->branch(s);
    return at_Undef;
  }

  brancher* b;
};
brancher* limit_brancher(brancher* b) { return new limit_branch(b); }

class warmstart_branch : public brancher {
public:
  enum State { Done = 0, Active = 1, Idle = 2 };
  warmstart_branch(vec<patom_t>& _decs)
    : decs(_decs), state(Idle), idx(0)
  { }

  inline bool atom_fixed(solver_data* s, patom_t at) {
    /*
    if(s->state.is_inconsistent(at)) {
      fprintf(stderr, "fskip.\n");
      return true;
    }
    if(s->state.is_entailed(at)) {
      fprintf(stderr, "sskip.\n");
      return true;
    }
    */
    return s->state.is_entailed(at) || s->state.is_inconsistent(at);
  }

  bool is_fixed(solver_data* s) {
    if(state == Done)
      return true;
    
    if(idx < decs.size()) {
      if(!atom_fixed(s, decs[idx]))
        return false;
      int ii = idx;      
      for(; ii < decs.size(); ++ii) {
        patom_t at(decs[ii]);
        if(atom_fixed(s, at))
          continue;
        idx.set(s->persist, ii); 
        return false;
      }
    }
    state = Done;
    return true;
  }

  patom_t branch(solver_data* s) {
    if(state == Done)
      return at_Undef;
    if(state == Idle) {
      // s->persist.bt_flags.push(&state);
      state = Active;
    }

    // static unsigned int c = 0;
    if(idx < decs.size()) {
      if(!atom_fixed(s, decs[idx]))
        return decs[idx];
      int ii = idx;
      for(; ii < decs.size(); ++ii) {
        patom_t at(decs[ii]);
        if(atom_fixed(s, at))
          continue;

        idx.set(s->persist, ii);
        // fprintf(stderr, "A(%d)\n", ++c);
        return at;
      }
    }
    // fprintf(stderr, "Finished after: %d\n", c);
    state = Done;
    return at_Undef;
  }

  vec<patom_t> decs;
  char state;
  Tint idx;
};

brancher* warmstart_brancher(vec<patom_t>& decs) { return new warmstart_branch(decs); }


class toggle_branch : public brancher
  /*, public evt<toggle_branch>*/ {
  void toggle(void) {
    ++active;
    if(active >= bs.size())
      active = 0;
      // active = bs.size()-1;
  }
public:
  toggle_branch(vec<brancher*> _bs)
    : bs(_bs), active(0), last_restart(0) {
    // s.on_restart.push(event<&E::toggle>());
  }

  bool is_fixed(solver_data* s) {
    return bs[active]->is_fixed(s);
  }

  patom_t branch(solver_data* s) {
    if(s->stats.restarts != last_restart) {
      toggle();
      last_restart = s->stats.restarts;
    }
    return bs[active]->branch(s);
  }
  vec<brancher*> bs;
  int active;
  int last_restart;
};
brancher* toggle_brancher(vec<brancher*>& bs) {
  return new toggle_branch(bs);
}

brancher* select_inorder_brancher(ValChoice val_choice, vec<pid_t>& preds) {
  switch(val_choice) {
    case Val_Min:
      return new inorder_branch<Val_Min>(preds);
    case Val_Max:
      return new inorder_branch<Val_Max>(preds);
    case Val_Split:
      return new inorder_branch<Val_Split>(preds);
    case Val_Saved:
      return new inorder_branch<Val_Saved>(preds);
    default:
      GEAS_NOT_YET;
      return nullptr;
  }
}

template<int VarC>
brancher* select_basic_brancher(ValChoice val_choice, vec<pid_t>& preds) {
  switch(val_choice) {
    case Val_Min:
      return new basic_branch<VarC, Val_Min>(preds);
    case Val_Max:
      return new basic_branch<VarC, Val_Max>(preds);
    case Val_Split:
      return new basic_branch<VarC, Val_Split>(preds);
    case Val_Saved:
      return new basic_branch<VarC, Val_Saved>(preds);
    default:
      GEAS_NOT_YET;
      return nullptr;
  }
}

brancher* basic_brancher(VarChoice var_choice, ValChoice val_choice, vec<pid_t>& preds) {
  switch(var_choice) {
    case Var_InputOrder:
      return select_inorder_brancher(val_choice, preds);
    case Var_FirstFail:
      return select_basic_brancher<Var_FirstFail>(val_choice, preds);
    case Var_Smallest:
      return select_basic_brancher<Var_Smallest>(val_choice, preds);
    case Var_Largest:
      return select_basic_brancher<Var_Largest>(val_choice, preds);
    default:
      GEAS_NOT_YET;
      return nullptr;
  }
}

class pred_act_brancher : public brancher {
public:
  pred_act_brancher(solver_data* _s)
    : s(_s), /* valb(_s), */ rem_count(0) { }
  
  bool is_fixed(solver_data* s) {
    if(s->pred_heap.empty())
      return true;

    while(!s->pred_heap.empty()) {
      int pi = s->pred_heap.getMin();
      
      // if(!pred_fixed(s, pi))
      if(!pred_fixed(s, pi<<1))
      {
        if(rem_count != removed.size()) {
          trail_push(s->persist, rem_count);
          rem_count = removed.size();
        }
        return false;
      }

      s->pred_heap.removeMin();
      removed.push(pi);
    }
    trail_push(s->persist, rem_count);
    rem_count = removed.size();

    return true;
  }

  patom_t branch(solver_data* s) {
    // Restore not-necessarily-fixed predicates
    // upon backtracking
    if(rem_count < removed.size()) {
      for(int xi : irange(rem_count, removed.size())) {
        s->pred_heap.insert(removed[xi]);
      }
      removed.shrink(removed.size() - rem_count);
    }

    pid_t pi = pid_None;
    while(!s->pred_heap.empty()) {
      pi = s->pred_heap.getMin();
      
      // if(!pred_fixed(s, pi))
      if(!pred_fixed(s, pi<<1))
      {
        if(rem_count != removed.size()) {
          trail_push(s->persist, rem_count);
          rem_count = removed.size();
        }

        // Choose a value to branch on. Currently [| pi = lb(pi) |]
        // return ~patom_t(pi, pred_val(s, pi<<1)+1);
        // return branch_val<Val_Pol>::branch(s, pi<<1);
//        return valb.branch(s, pi<<1);
        // return branch_val<Val_Min>::branch(s, pi<<1);
        // return branch_val<Val_Max>::branch(s, pi<<1);
        return branch_val<Val_Saved>::branch(s, pi<<1);
      }

      s->pred_heap.removeMin();
      removed.push(pi);
    }
    // No preds remain
    return at_Undef;
  }

  solver_data* s;
//  prog_branch valb;

  // Used for restoration 
  vec<int> removed;
  int rem_count;
};

class atom_act_brancher : public brancher {
public:
  atom_act_brancher(solver_data* _s)
    : s(_s) {
       
  }

  patom_t branch(solver_data* s) {
    GEAS_NOT_YET;
    return at_Undef;
  }

  solver_data* s;
};

brancher* pred_act_branch(solver_data* s) {
  return new pred_act_brancher(s);
}

brancher* atom_act_branch(solver_data* s);
brancher* default_brancher(solver_data* s) {
//  return new simple_branch();
  return pred_act_branch(s);
}

patom_t branch(solver_data* s) {
  for(brancher* b : s->branchers) {
    patom_t p = b->branch(s);
    if(p != at_Undef)
      return p;
  }
  return s->last_branch->branch(s);
}

}
