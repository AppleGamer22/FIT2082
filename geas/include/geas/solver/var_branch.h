#ifndef GEAS_VAR_BRANCH__H
#define GEAS_VAR_BRANCH__H
#include <geas/solver/branch.h>

namespace geas {

template<class V>
class var_chooser {
public:
  var_chooser(VarChoice _varC)
    : varC(_varC) { }

  int64_t score(solver_data* s, const V& x) {
    switch(varC) {
      case Var_InputOrder:
        return 0;
      case Var_FirstFail:
        // return x.dom_sz_exact(s->state.p_vals);
        return x.ub(s) - x.lb(s);
      case Var_Smallest:
        return x.lb(s);
      case Var_Largest:
        return -x.ub(s);
      default:
        return 0;
    }
  }

  VarChoice varC;
};

template<class V>
class val_chooser {
public:
  val_chooser(ValChoice _valC)
    : valC(_valC) { }

   patom_t branch(solver_data* s, const V& x) const {
    switch(valC) {
      case Val_Min:
        return x <= x.lb(s);
      case Val_Max:
        return x >= x.ub(s);
      case Val_Split:
        {
        auto mid(x.lb(s) + ((x.ub(s) - x.lb(s))/2));
        return x <= mid;
        }
        /*
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
        */
      default:
        GEAS_NOT_YET; 
        return at_Error;
    }
  }

  ValChoice valC;
};

template<class V, class Score, class Sel>
class score_brancher : public brancher {
public:
  score_brancher(Score _score, Sel _sel, vec<V>& _xs)
    : score(_score), sel(_sel), xs(_xs), low(0) { }

  ~score_brancher(void) { }

  patom_t branch(solver_data* s) {
    if(!is_fixed(s)) {
      int best(low);
      int64_t best_score(score.score(s, xs[low]));
      for(int ii = low+1; ii < xs.size(); ++ii) {
        if(xs[ii].is_fixed(s))
          continue;
        int64_t x_score(score.score(s, xs[ii]));
        if(x_score < best_score) {
          best = ii;
          best_score = x_score;
        }
      }
      // Select a branch
      return sel.branch(s, xs[best]);
    }
    return at_Undef;
  }

  bool is_fixed(solver_data* s) {
    if(low < xs.size()) {
      if(!xs[low].is_fixed(s))
        return false;
      for(int ii = low+1; ii < xs.size(); ++ii) {
        if(!xs[ii].is_fixed(s)) {
          low.set(s->persist, ii);
          return false;
        }
      }
      low.set(s->persist, xs.size());
    }
    return true;
  }

  Score score;
  Sel sel;
  vec<V> xs;
  Tint low;
};

/*
template<class P, class V, class Score, class Sel>
class priority_brancher : public brancher {
  priority_brancher(Sel _sel, vec<P>& _ps, vec<V>& _xs)
    : sel(_sel), ps(_ps), xs(_xs), low(0) { }

  ~priority_brancher(void) { }

  patom_t branch(solver_data* s) {
    if(!is_fixed(s)) {
      int best(low);
      size_t best_score(score(s, ps[low]));
      for(int ii = low+1; ii < xs.size(); ++ii) {
        if(xs[ii].is_fixed(s))
          continue;
        size_t x_score(score(s, ps[ii]));
        if(x_score < best_score) {
          best = ii;
          best_score = x_score;
        }
      }
      // Select a branch
      return sel.choose(s, xs[best]);
    }
    return at_Undef;
  }

  bool is_fixed(solver_data* s) {
    if(low < xs.size()) {
      if(!xs[low].is_fixed(s))
        return false;
      for(int ii = low+1; ii < xs.size(); ++ii) {
        if(!xs[ii].is_fixed(s)) {
          low.set(s->persist, ii);
          return false;
        }
      }
      set(low, xs.size());
    }
    return true;
  }

  Score score;
  Sel sel;
  vec<P> ps;
  vec<V> xs;
  Tint low;
};
*/

};

#endif
