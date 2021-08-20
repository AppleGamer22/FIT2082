#ifndef GEAS_PRIORITY_BRANCH__H
#define GEAS_PRIORITY_BRANCH__H
#include <climits>
#include <geas/solver/branch.h>

namespace geas {
namespace branching {

template<int VarC, class V>
forceinline int score(solver_data* s, V x) {
    ctx_t& ctx(s->state.p_vals);
    switch(VarC) {
      case Var_Smallest:
        return x.lb(ctx);
      case Var_Largest:
        return -x.ub(ctx);
      case Var_FirstFail:
        return x.ub(ctx) - x.lb(ctx);
      default:
        return 0;
  }
}


template<int Sel, class V>
class priority : public brancher {
  struct elt { V x; brancher* b; };
public:
  priority(vec<V>& xs, vec<brancher*>& bs)
    : start(0) {
    for(int ii : irange(std::min(xs.size(), bs.size()))) {
      elts.push(elt { xs[ii], bs[ii] });
    }
  }

  bool is_fixed(solver_data* s) {
    elt* e = elts.begin() + start;
    elt* end = elts.end(); 

    if(e != end) {
      if(!e->b->is_fixed(s))
        return false;
      for(++e; e != end; ++e) {
        if(!e->b->is_fixed(s)) {
          start.set(s->persist, e - elts.begin());
          return false;
        }
      }
      start.set(s->persist, elts.size());
    }
    return true;
  }

  patom_t branch(solver_data* s) {
    elt* e = elts.begin() + start;
    elt* end = elts.end();
    // Find the best
    int opt = INT_MAX;
    elt* sel = elts.end();
    for(; e != end; ++e) {
      if(e->b->is_fixed(s))
        continue;

      int sc = score<Sel, V>(s, e->x);
      if(sc < opt) {
        opt = sc;
        sel = e;
      }
    }
    if(sel != end)
      return sel->b->branch(s);
    return at_Undef;
  }
  
  vec<elt> elts;
  // Trailed start of 'live' branchers
  Tint start;
};

};

template<class V>
brancher* priority_brancher(VarChoice sel, vec<V>& xs, vec<brancher*>& br) {
  switch(sel) {
    case Val_Min:
      return new branching::priority<Val_Min, V>(xs, br);
    case Val_Max:
      return new branching::priority<Val_Max, V>(xs, br);
    case Val_Split:
      return new branching::priority<Val_Split, V>(xs, br);
    case Val_Saved:
      return new branching::priority<Val_Saved, V>(xs, br);
    default:
      GEAS_NOT_YET;
      return nullptr;
  }
}

}
#endif
