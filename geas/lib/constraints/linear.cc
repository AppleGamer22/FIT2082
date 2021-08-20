#include <cassert>
#include <map>
#include <climits>
#include <geas/mtl/Vec.h>
#include <geas/solver/solver_data.h>
#include <geas/mtl/min-tree.h>
#include <geas/vars/intvar.h>

#include <geas/engine/propagator_ext.h>

// #define USE_CHAIN
#define SKIP_L0
// #define EXPL_EAGER
// #define EXPL_NAIVE

namespace geas {

struct elt {
   elt(int _c, intvar _x)
     : c(_c), x(_x) { }
  int c;
  intvar x;
};

int normalize_linex(solver_data* s, const vec<int>& ks, const vec<intvar>& vs, int k, vec<elt>& out) {
  // Make sure we merge any identical terms.
  out.clear();
  vec<elt> trim_elts;
  for(int ii = 0; ii < vs.size(); ++ii) {
    trim_elts.push(elt(ks[ii], vs[ii]));
  }
  std::sort(trim_elts.begin(), trim_elts.end(),
            [](const elt& a, const elt& b) { return a.x.p < b.x.p; });

  elt* b_it = trim_elts.begin();
  elt* b_en = trim_elts.end();
  elt curr = *b_it;

  for(++b_it; b_it != b_en; ++b_it) {
    if(curr.x.p == b_it->x.p) {
      curr.c += b_it->c;
      k -= b_it->c*(b_it->x.off -curr.x.off);
    } else if(curr.x.p == (b_it->x.p^1)) {
      // x' = -x + k (for some k).
      intvar xP = -b_it->x;
      curr.c -= b_it->c;
      k -= b_it->c*(xP.off - curr.x.off);
    } else {
      if(curr.c > 0) {
        out.push(curr);
      } else if(curr.c < 0) {
        out.push(elt(-curr.c, -curr.x));
      }
      curr = *b_it;
    }
  }
  if(curr.x.lb(s->ctx()) == curr.x.ub(s->ctx())) {
    k -= curr.c * curr.x.lb(s->ctx());
  } else if(curr.c > 0) {
    out.push(curr);
  } else if(curr.c < 0) {
    out.push(elt(-curr.c, -curr.x));
  }
  return k;
}
void normalize_linex_inplace(solver_data* s, vec<int>& ks, vec<intvar>& vs, int& k) {
  vec<elt> xs;
  k = normalize_linex(s, ks, vs, k, xs);
  ks.clear();
  vs.clear();
  for(const elt& e : xs) {
    ks.push(e.c);
    vs.push(e.x);
  }
}

class int_linear_le : public propagator, public prop_inst<int_linear_le> {
  enum { Var_None = -1 };

  /*
  static void wake_x(void* ptr, int xi) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr)); 
    p->queue_prop();     
  }
  static void wake_y(void* ptr, int yi) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr)); 
    p->queue_prop();     
  }
  */
  watch_result wake_x(int xi) { queue_prop(); return Wt_Keep; }
  watch_result wake_y(int xi) { queue_prop(); return Wt_Keep; }
  
  /*
  struct elt {
    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;
  };
  */

  // Requires backtracking
  void ex_naive(int ei, vec<clause_elt>& expl) {
    for(int xi = 0; xi < xs.size(); xi++) {
      if(xi == ei)
        continue;
      expl.push(xs[xi].x < xs[xi].x.lb(s));
    }
    /*
    for(elt e : p->xs)
      expl.push(e.x < e.x.lb(s));
    for(elt e : p->ys)
      expl.push(e.x > e.x.ub(s));
      */
  }

  static void ex_x(void* ptr, int xi, pval_t pval,
                       vec<clause_elt>& expl) {
    int_linear_le* p(static_cast<int_linear_le*>(ptr));
#ifndef EXPL_NAIVE
    intvar::val_t ival(to_int(pval_inv(pval))+p->xs[xi].x.off);
    intvar::val_t lim(p->k - p->xs[xi].c*(ival+1) + 1);

    intvar::val_t sum = 0;
    for(int xj : irange(xi))
      sum += p->xs[xj].c * p->xs[xj].x.lb(p->s);
    for(int xj : irange(xi+1, p->xs.size()))
      sum += p->xs[xj].c * p->xs[xj].x.lb(p->s);
    p->make_expl(xi, sum - lim, expl);
#else
    // Naive explanation
    for(elt e : p->xs) {
      assert(p->s->state.is_inconsistent(e.x < e.x.lb(p->s)));
      expl.push(e.x < e.x.lb(p->s));
    }
#endif
  }


  public: 

    int_linear_le(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), k(_k)
      {
        if(!s->state.is_entailed_l0(_r))
          assert(0 && "int_linear_le doesn't support reification!");
      k = normalize_linex(s, ks, vs, k, xs);
      for(int ii = 0; ii < xs.size(); ii++) {
        xs[ii].x.attach(E_LB, watch<&P::wake_x>(ii, Wt_IDEM));
      }
    }

    void root_simplify(void) {
      
    }
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      assert(slack >= 0);
#if 0
      for(elt e : xs) {
        assert(s->state.is_inconsistent(e.x < e.x.lb(s)));
        ex.push(e.x < e.x.lb(s));
      }
      for(elt e : ys) {
        assert(s->state.is_inconsistent(e.x > e.x.ub(s)));
        ex.push(e.x > e.x.ub(s));
      }
#else
      vec<int> xs_pending;
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      for(int xi : irange(0, xs.size())) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb(s);
#ifndef SKIP_L0
        int x_lb_0 = lb_0(e.x);
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
#endif
        int x_lb_p = lb_prev(e.x);
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          ex.push(e.x < x_lb_p); 
          continue;
        }
        xs_pending.push(xi);
      }

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        ex.push(e.x < e.x.lb(s) - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
#endif
    }

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le]]" << std::endl;
#endif
      int x_lb = 0;
      for(elt e : xs)
        x_lb += e.c * e.x.lb(s);

      if(x_lb > k) {
        // Collect enough atoms to explain the sum.
        // FIXME: This is kinda weak. We really want to
        // push as much as we can onto the previous level.
        make_expl(Var_None, x_lb - k - 1, confl);
        /* /
        for(elt e : xs)
          confl.push(e.x < e.x.lb(s));
        for(elt e : ys)
          confl.push(e.x > e.x.ub(s));
        / */

        // GEAS_NOT_YET;
#ifdef CHECK_STATE
        assert(confl_is_current(s, confl));
#endif
        return false; 
      }

      // Otherwise, propagate upper bounds.
      int slack = k - x_lb;
      for(int xi : irange(0, xs.size())) {
        elt e = xs[xi];
        int x_diff = slack/e.c;
        int x_ub = e.x.lb(s) + x_diff;
        if(x_ub < e.x.ub(s)) {
          // Build the explanation
          /*
          expl_builder ex(s->persist.alloc_expl(xs.size()+ys.size()));
          make_expl(2*xi, slack - e.c * x_diff, ex);
          if(!e.x.set_ub(x_ub, *ex))
          */
          if(!set_ub(e.x, x_ub,
              expl_thunk { ex_x, this, xi, expl_thunk::Ex_BTPRED }))
//            if(!e.x.set_ub(x_ub,
//                ex_thunk(ex_nil<&P::ex_naive>, 2*xi, expl_thunk::Ex_BTPRED)))
            return false;
        }
      }

      return true;
    }

    vec<elt> xs;
    int k;
};

// Incremental linear le propagator
class lin_le_inc : public propagator, public prop_inst<lin_le_inc> {
  enum { Var_None = -1 };
  enum { S_Active = 1, S_Red = 2 };
  
  /*
  struct elt {
    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;
  };
  */

  forceinline int delta(int c, pid_t p) {
    return c * (s->state.p_vals[p] - s->wake_vals[p]);
  }

  int compute_lb(void) {
    int lb = 0;
    for(const elt& e : xs)
      lb += e.c * e.x.lb(s);
    return lb;
  }

  watch_result wake_r(int xi) {
    trail_change(s->persist, status, (char) S_Active);

    // Compute the threshold
    int new_threshold = 0;
    for(const elt& e : xs)
      new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub(s) - e.x.lb(s))));
    if(slack < new_threshold) {
      queue_prop();
    } else {
//      trail_change(s->persist, threshold, new_threshold);
      set(threshold, new_threshold);
    }
    return Wt_Keep;
  }

  watch_result wake_x(int xi) {
    if(status&S_Red)
      return Wt_Keep;

    trail_change(s->persist, slack, slack - delta(xs[xi].c, xs[xi].x.p));
#ifdef CHECK_STATE
    // Might not have processed all watches yet
    assert(slack >= k - compute_lb());
#endif
    if(slack < threshold)
      queue_prop();
    return Wt_Keep;
  }

  // Requires backtracking
  void ex_naive(int ei, vec<clause_elt>& expl) {
    for(int xi = 0; xi < xs.size(); xi++) {
      if(xi == ei)
        continue;
      expl.push(xs[xi].x < xs[xi].x.lb(s));
    }
  }

  void ex_r(int ex_slack, vec<clause_elt>& expl) {
    make_expl(Var_None, ex_slack, expl);
  }

  template<class T>
  inline void EX_PUSH(T& expl, patom_t at) {
    assert(!ub(at));
    expl.push(at);
  }

  void ex_x(int xi, pval_t pval, vec<clause_elt>& expl) {
#ifndef EXPL_NAIVE
    intvar::val_t ival(xs[xi].x.ub_of_pval(pval));
    intvar::val_t lim(k - xs[xi].c*(ival+1) + 1);

    intvar::val_t sum = 0;
    for(int xj : irange(xi))
      sum += xs[xj].c * xs[xj].x.lb(s);
    for(int xj : irange(xi+1, xs.size()))
      sum += xs[xj].c * xs[xj].x.lb(s);
    EX_PUSH(expl, ~r);
    make_expl(xi, sum - lim, expl);
#else
    // Naive explanation
    expl.push(~r);
    for(elt e : xs) {
      assert(s->state.is_inconsistent(e.x < e.x.lb(s)));
      expl.push(e.x < e.x.lb(s));
    }
#endif
  }


  public: 

    lin_le_inc(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& vs, int _k)
      : propagator(s), r(_r), k(_k), slack(k), threshold(0), status(0)
      {
        // Normalize to remove any redundant/aliased terms.
        k = normalize_linex(s, ks, vs, k, xs);
        for(int ii = 0; ii < xs.size(); ++ii) {
          xs[ii].x.attach(E_LB, watch<&P::wake_x>(ii, Wt_IDEM));
        }
          /*
      for(int ii = 0; ii < vs.size(); ii++) {
        elt e = ks[ii] > 0 ? elt(ks[ii], vs[ii]) : elt(-ks[ii], -vs[ii]);
        e.x.attach(E_LB, watch<&P::wake_x>(xs.size(), Wt_IDEM));
        xs.push(e);
      }
          */
      // Initialize lower bound
      for(const elt& e : xs)
        slack -= e.c * lb_prev(e.x);
      // Tighten upper bound, and compute threshold? 
      if(s->state.is_entailed(r)) {
        status = S_Active;
        for(elt& e : xs) {
          int x_ub = e.x.lb(s) + slack/e.c;
          if(x_ub < e.x.ub(s))
            set_ub(e.x, x_ub, reason());
          // threshold = std::max(threshold, (int) (e.c * (e.x.ub(s) - e.x.lb_prev())));
          threshold.x = std::max(threshold.x, (int) (e.c * (e.x.ub(s) - lb_prev(e.x))));
        }
#ifdef CHECK_STATE
        assert(slack >= k - compute_lb());
#endif
      } else {
        attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
        for(elt& e : xs) {
          int x_ub = e.x.lb(s) + slack/e.c;
          if(x_ub < e.x.ub(s))
            add_clause(s, ~r, e.x <= x_ub);
        }
        threshold.x = 0;
      }
    }

    void root_simplify(void) {
        
    }
    
    template<class E>
    void make_expl(int var, int slack, E& ex) {
      assert(slack >= 0);

#if 0
      for(int xi = xs.size()-1; xi >= 0; --xi) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = lb(e.x);
        int x_lb_prev = lb_prev(e.x);

        int diff = e.c * (x_lb - x_lb_prev);
        if(diff <= slack) {
          slack -= diff;

          diff = e.c * (x_lb_prev - lb_0(e.x));
          if(diff <= slack) {
            slack -= diff;
            continue;
          }
          ex.push(e.x < x_lb_prev); 
          continue;
        }
        ex.push(e.x < x_lb);
      }
#else
      // First, collect things we can omit entirely, or
      // include at the previous decision level
      vec<int> xs_pending;
      for(int xi : irange(0, xs.size())) {
        if(xi == var)
          continue;
        elt e = xs[xi];

        int x_lb = e.x.lb(s);
        int x_lb_0 = lb_0(e.x);
        int diff_0 = e.c * (x_lb - x_lb_0);
        if(diff_0 <= slack) {
          slack -= diff_0;
          continue;
        }
        xs_pending.push(xi);
      }

      /*
      int* xp = xs_pending.begin();
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int x_lb = e.x.lb(s);
        int x_lb_p = lb_prev(e.x);
        int diff_p = e.c * (x_lb - x_lb_p);
        if(diff_p <= slack) {
          slack -= diff_p;
          EX_PUSH(ex, e.x < x_lb_p); 
          continue;
        }
        *xp = xi; ++xp;
      }
      xs_pending.shrink_(xs_pending.end() - xp);
      */

      // Then, add things at the current level
      assert(slack >= 0);
      for(int xi : xs_pending) {
        elt e = xs[xi];
        int diff = slack/e.c;
        EX_PUSH(ex, e.x < e.x.lb(s) - diff);
        slack -= e.c * diff;
        assert(slack >= 0);
      }
#endif
    }

    bool check_sat(ctx_t& ctx) {
      int low = 0;
      for(elt e : xs) {
        low += e.c * e.x.lb(ctx);
      }
      return !r.lb(ctx) || low <= k;
    }
    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
      std::cout << "[[Running linear_le(inc)]]" << std::endl;
#endif
#ifdef CHECK_STATE
      assert(slack == k - compute_lb());
#endif
      /*
      static unsigned int count = 0;
      static unsigned int lim = 1000;
      */

      if(status&S_Red)
        return false;

      if(slack < 0) {
        // Collect enough atoms to explain the sum.
        // FIXME: This is kinda weak. We really want to
        // push as much as we can onto the previous level.
        if(!enqueue(*s, ~r, ex_thunk(ex_nil<&P::ex_r>, -slack-1, expl_thunk::Ex_BTPRED)))
          return false;
        trail_change(s->persist, status, (char) S_Red);
        return true;
#ifdef CHECK_STATE
//        assert(confl_is_current(s, confl));
#endif
      }

      if(!(status&S_Active))
        return true;

      /*
      if(++count > lim) {
        fprintf(stderr, "lin_le_inc: %d\n", count);
        lim *= 1.1;
      }
      */

      // Otherwise, propagate upper bounds.
//      int slack = k - lb;
      int new_threshold = 0;
      for(int xi : irange(0, xs.size())) {
        elt e = xs[xi];
        int x_diff = slack/e.c;
        int x_ub = e.x.lb(s) + x_diff;
        if(x_ub < e.x.ub(s)) {
          // Build the explanation
          if(!set_ub(e.x, x_ub,
              ex_thunk(ex<&P::ex_x>, xi, expl_thunk::Ex_BTPRED)))
            return false;
        }
        new_threshold = std::max(new_threshold, (int) (e.c * (e.x.ub(s) - e.x.lb(s))));
      }

      // trail_change(s->persist, threshold, new_threshold);
      set(threshold, new_threshold);
      return true;
    }

    patom_t r;
    vec<elt> xs;
    int k;

    // Persistent state
    int slack;
    // int threshold;
    Tint threshold;
    char status;
};

int succ(int k) { return k+1; }
template<class V, class R>
class lin_le_mtree : public propagator, public prop_inst<lin_le_mtree<V, R> > {
  // How much could xi increase the total by?
  typedef lin_le_mtree<V, R> P;
  struct term {
    V c;
    R x;
  };

  V envelope(ctx_t& ctx, int xi) {
    return xs[xi].c * (xs[xi].x.ub(ctx) - xs[xi].x.lb(ctx)); 
  }
  // How much has the total just increased by?
  V delta(int xi) {
    return xs[xi].c * (xs[xi].x.lb(s->state.p_vals) - xs[xi].x.lb(s->wake_vals));
  }

  struct MaxEnv {
    V operator()(solver_data* s, int ii) { return -p->envelope(s->state.p_vals, ii); }
    lin_le_mtree<V, R>* p;
  };

  watch_result wake_r(int _r) {
    if(mt.root_val() < -slack)
      queue_prop();
    return Wt_Keep;
  }

  watch_result wake_x(int xi) {
    // Update slack.
    set(slack, slack - delta(xi));
    if(mt.root_val() < -slack) {
      if(lb(r) || slack < 0)
        queue_prop();
    }
    return Wt_Keep;
  }

  // Explain why sum (i != skip) (c_i x_i) > cap.
  void ex_overload(V cap, int skip, vec<clause_elt>& expl) {
    vec<int> ex_vars;
    // Collect root contributions.
    for(int xi : irange(xs.size())) {
      if(xi == skip)
        continue;
      cap -= xs[xi].c * lb_0(xs[xi].x);
    }
    if(cap < 0)
      return;
    for(int xi : irange(xs.size())) {
      if(xi == skip)
        continue;
     
      V diff(xs[xi].c * (lb(xs[xi].x) - lb_0(xs[xi].x)));
      if(diff == 0)
        continue;
      ex_vars.push(xi);
      if(diff > cap) {
        V avail(diff - succ(cap));
        // Walk back through the vars, relaxing where we can.
        for(int xi : ex_vars) {
          V diff = xs[xi].c * (lb(xs[xi].x) - lb_0(xs[xi].x));
          if(diff <= avail) {
            avail -= diff;
            continue;
          }
          V diff_p = xs[xi].c * (lb(xs[xi].x) - lb_prev(xs[xi].x));
          if(diff_p <= avail) {
            avail -= diff_p;
            EX_PUSH(expl, xs[xi].x < lb_prev(xs[xi].x));
            continue;
          }
          V delta = avail/xs[xi].c;
          avail -= delta * xs[xi].c;
          EX_PUSH(expl, xs[xi].x < lb(xs[xi].x) - delta);
        }
        return;
      } else {
        cap -= diff;
      }
    }
    // If we reach here, we've processed all variables
    // without overload.
    GEAS_ERROR;
  }

  void ex_r(int _r, pval_t _p, vec<clause_elt>& expl) {
    // We need to collect a set of atoms exceeding k.
    // assert(compute_lb() > k);
    ex_overload(k, -1, expl);
  }
  void ex_x(int xi, pval_t p, vec<clause_elt>& expl) {
    EX_PUSH(expl, ~r);
    V x_ub(xs[xi].x.ub_of_pval(p));
    // assert(compute_lb() + xs[xi].c * (succ(x_ub) - xs[xi].x.lb(s)) > k);
    ex_overload(k - xs[xi].c * succ(x_ub), xi, expl);
  }

public:
  lin_le_mtree(solver_data* s, patom_t _r, vec<V>& cs, vec<R>& vs, V _k)
    : propagator(s), r(_r), xs(), k(_k), mt(s, MaxEnv {this}, 0), slack(k) {
    // Normalize coefficients as usual.
    for(int ii : irange(vs.size())) {
      V c(cs[ii]);
      R v(vs[ii]); 

      if(c < 0) {
        c = -c;
        v = -v;
      }
      V v_p(lb_prev(v));
      if(v_p != 0) {
        k -= c * v_p;
        v -= v_p;
      }
      v.attach(E_LB, this->template watch<&P::wake_x>(xs.size(), P::Wt_IDEM));
      xs.push(term { c, v });
    }
    set(slack, k);
    mt.rebuild(s, xs.size());

    if(!lb(r)) {
      attach(s, r, this->template watch<&P::wake_r>(0, P::Wt_IDEM));
    }
  }
  V compute_lb(void) {
    V l(0);  
    for(term t : xs)
      l += t.c * lb(t.x);
    return l;
  }
  bool propagate(vec<clause_elt>& confl) {
    // assert(slack == k - compute_lb());
    if(slack < 0) {
      if(!enqueue(*s, ~r, this->template expl<&P::ex_r>(0, expl_thunk::Ex_BTPRED)))
        return false;
    }
    if(!lb(r))
      return true;

    return mt.forall_lt([&](int xi) {
      V cap = lb(xs[xi].x) + slack/(xs[xi].c);
      // std::cerr << "Setting var " << xi << " to " << cap << std::endl;
      return set_ub(xs[xi].x, cap, this->template expl<&P::ex_x>(xi, expl_thunk::Ex_BTPRED));
    }, s, -slack);
  }

  bool check_sat(ctx_t& ctx) {
    V l(0);
    for(term t : xs)
      l += t.c * t.x.lb(ctx);

    return !r.lb(ctx) || l <= k;
  }
  bool check_unsat(ctx_t& ctx) {
    return !check_sat(ctx);
  }

  patom_t r;
  vec<term> xs;
  V k;

  // We use a weak_min_tree, but we never call repair_min;
  // just forall_lt.
  weak_min_tree<V, MaxEnv> mt;
  Tint slack;
};

class int_linear_ne : public propagator, public prop_inst<int_linear_ne> {
  enum { Var_None = 0, Var_LB = 1, Var_UB = 2 };
  enum { S_Active = 1, S_Red = 2 };

  enum TrigKind { T_Atom, T_Var };
  struct trigger {
    TrigKind kind;
    unsigned int idx;
  };
  
  inline bool is_triggered(trigger t) {
    switch(t.kind) {
      case T_Atom:
        return s->state.is_entailed(r);
      case T_Var:
        return vs[t.idx].x.is_fixed(s);
      default:
        GEAS_ERROR;
        return false;
    }
  }

  inline void attach_trigger(trigger t, int ii) {
    switch(t.kind) {
      case T_Atom:
        attach(s, r, watch<&P::wake_trig>(ii, Wt_IDEM));
        break;
      case T_Var:
        vs[t.idx].x.attach(E_FIX, watch<&P::wake_trig>(ii, Wt_IDEM));
        break;
    }
  }

  // See if we can find some other unfixed variable
  watch_result wake_bound(int vi) {
    if(!(status&S_Active) || !is_triggered(trigs[1 - t_act]))
      return Wt_Drop;

    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_trig(int ti) {
    // Look for a replacement watch
    for(int ii = 2; ii < trigs.size(); ii++) {
      if(!is_triggered(trigs[ii])) {
        std::swap(trigs[ti], trigs[ii]);
        attach_trigger(trigs[ti], ti);  
        return Wt_Drop;
      }
    }
    // None found
    if(!is_triggered(trigs[1 - ti]))
      t_act = 1 - ti;
    queue_prop();
    return Wt_Keep;
  }

  inline void ex_trig(trigger t, vec<clause_elt>& expl) {
    switch(t.kind) {
      case T_Atom:
        EX_PUSH(expl, ~r);
        return;
      case T_Var:
#if 0
        EX_PUSH(expl, vs[t.idx].x < vs[t.idx].x.lb(s));
        EX_PUSH(expl, vs[t.idx].x > vs[t.idx].x.ub(s)); 
#else
        EX_PUSH(expl, vs[t.idx].x != vs[t.idx].x.lb(s));
#endif
        return;
    }
  }

  void explain(int xi, vec<clause_elt>& expl) {
    ex_trig(trigs[1 - t_act], expl);
    for(int ti = 2; ti < trigs.size(); ti++)
      ex_trig(trigs[ti], expl);

    if(xi&E_LB)
      EX_PUSH(expl, vs[t_act].x < excl_val);
    if(xi&E_UB)
      EX_PUSH(expl, vs[t_act].x > excl_val);
  }

  void ex_xi(int xi, pval_t _p, vec<clause_elt>& expl) {
    EX_PUSH(expl, ~r);
    for(int ii = 0; ii < vs.size(); ++ii) {
      if(ii == xi)
        continue;
#if 1
      vs[ii].x.explain_eq(lb(vs[ii].x), expl);
#else
      EX_PUSH(expl, vs[ii].x < lb(vs[ii].x));
      EX_PUSH(expl, vs[ii].x > ub(vs[ii].x));
#endif
    }
  }
  void ex_r(int _r, pval_t _p, vec<clause_elt>& expl) {
    for(int ii = 0; ii < vs.size(); ++ii) {
#if 1
      vs[ii].x.explain_eq(lb(vs[ii].x), expl);
#else
      EX_PUSH(expl, vs[ii].x < lb(vs[ii].x));
      EX_PUSH(expl, vs[ii].x > ub(vs[ii].x));
#endif
    }
  }


public:
  /*
  struct elt {
    elt(int _c, intvar _x)
      : c(_c), x(_x) { }
    int c;
    intvar x;
  };
  */
  
  int_linear_ne(solver_data* s, patom_t _r, vec<int>& ks, vec<intvar>& xs, int _k)
    : propagator(s), r(_r), k(_k), t_act(0), status(0) {
    assert(xs.size() >= 2);
    for(int ii = 0; ii < xs.size(); ii++) {
      // FIXME
      make_eager(xs[ii]);
      vs.push(elt(ks[ii], xs[ii]));
      trigs.push(trigger { T_Var, (unsigned int) ii });
    }
    if(!s->state.is_entailed(r)) {
      trigger t(trigs[0]);
      trigs.push(t);
      trigs[0] = { T_Atom };
    }
    attach_trigger(trigs[0], 0);
    attach_trigger(trigs[1], 1);
  }

#if 0
  bool check_sat(ctx_t& ctx) {
    int sum = 0; 
    for(auto t : vs) {
      if(!t.x.is_fixed(ctx))
        return true;
      sum += t.c * t.x.lb(ctx);
    }
    return !r.lb(ctx) || (sum != k);
  }
  bool check_unsat(ctx_t& ctx) {
    return !check_sat(ctx);
  }
#endif

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cout << "[[Running linear_ne]]" << std::endl;
#endif
#if 1
    if(status&S_Active) {
      int idx = trigs[t_act].idx;
      if(vs[idx].x.lb(s) == excl_val) {
        return set_lb(vs[idx].x, excl_val+1, ex_thunk(ex_nil<&P::explain>, E_LB));
      } else {
        assert(vs[idx].x.ub(s) == excl_val);
        return set_ub(vs[idx].x, excl_val-1, ex_thunk(ex_nil<&P::explain>, E_UB));
      }
    }

    if(trigs[t_act].kind == T_Atom) {
      intvar::val_t sum = k;
      for(const elt& e : vs)
        sum -= e.c * e.x.lb(s);

      if(sum)
        return true;
      return enqueue(*s, ~r, ex_thunk(ex_nil<&P::explain>, 0));
    } else {
      int vi = trigs[t_act].idx;
      intvar::val_t sum = k;
      for(int ii = 0; ii < vi; ii++)
        sum -= vs[ii].c * vs[ii].x.lb(s);
      for(int ii = vi+1; ii < vs.size(); ii++)
        sum -= vs[ii].c * vs[ii].x.lb(s);

      if(sum % vs[vi].c != 0) {
        excl_val = INT_MAX;
        return true;
      }
      
      // Check if it's already satisfied or propagatable.
      excl_val = sum/vs[vi].c;   
#if 0
      if(vs[vi].x.lb(s) >= excl_val) {
        if(vs[vi].x.lb(s) == excl_val)
          return set_lb(vs[vi].x,excl_val+1, ex_thunk(ex_nil<&P::expl>, E_LB));
        return true;
      } else if(vs[vi].x.ub(s) <= excl_val) {
        if(vs[vi].x.ub(s) == excl_val)
          return set_lb(vs[vi].x,excl_val-1, ex_thunk(ex_nil<&P::expl>, E_UB));
        return true;
      }
      
      // Otherwise, add the new watches
      trail_change(s->persist, status, (char) S_Active);
      attach(s, vs[vi].x >= excl_val, watch<&P::wake_bound>(0, Wt_IDEM));
      attach(s, vs[vi].x <= excl_val, watch<&P::wake_bound>(1, Wt_IDEM));
      return true;
#else
      if(vs[vi].x.lb(s) > excl_val)
        return true;
      if(vs[vi].x.ub(s) < excl_val)
        return true;
      return enqueue(*s, vs[vi].x != excl_val, ex_thunk(ex_nil<&P::explain>, 0));
#endif
    }
#else
    // Dumb, non-incremental version.
    int ii = 0;
    int total = k;
    for(; ii < vs.size(); ++ii) {
      if(!is_fixed(vs[ii].x)) {
        // If there's an un-fixed variable and r isn't set,
        // Don't bother.
        if(!lb(r))
          return true;
        // Otherwise, finish computing the sum.
        int jj = ii+1;
        for(; jj < vs.size(); ++jj) {
          if(!is_fixed(vs[jj].x))
            return true;
          
          total -= vs[jj].c * lb(vs[jj].x);
        }
        // Exactly one un-fixed variable
        if(total % vs[ii].c != 0)
          return true;
        int excl = total / vs[ii].c;
        if(!in_domain(vs[ii].x, excl))
          return true;
        if(!enqueue(*s, vs[ii].x != (total / vs[ii].c), expl<&P::ex_xi>(ii)))
          return false;
        return true;
      }
      total -= vs[ii].c * vs[ii].x.lb(s);
    }
    // Finished computing the sum.
    if(total == 0) {
      if(!enqueue(*s, ~r, expl<&P::ex_r>(0)))
        return false;
    }
#endif
    return true;
  }

  // virtual bool check_sat(void) { return true; }
  // void root_simplify(void) { }
  patom_t r;

  vec<elt> vs;
  int k;

  vec<trigger> trigs;
  unsigned int t_act;
  char status;
  intvar::val_t excl_val;
};

struct term {
  int k;
  intvar x;

  int lb(solver_data* s) const { return k * x.lb(s); }
  int ub(solver_data* s) const { return k * x.ub(s); }
};

intvar make_ps(solver_data* s, patom_t r, term tx, term ty, int k) {
  int ub = std::min(k, tx.ub(s) + ty.ub(s));
  intvar ps = new_intvar(s, 0, ub);
  vec<int> ks { tx.k, ty.k, -1 };
  vec<intvar> xs { tx.x, ty.x, ps };
  lin_le_inc::post(s, r, ks, xs, 0);
  return ps;
}
bool linear_le_chain(solver_data* s, patom_t r, vec<int>& ks, vec<intvar>& vs, int k) {
  if(ks.size() <= 2) {
    lin_le_inc::post(s, r, ks, vs, k);
    return true;
  }
  // Normalize the terms, correcting for lower bounds.
  vec<term> xs;
  for(int ii = 0; ii < ks.size(); ii++) {
    term t = ks[ii] < 0 ? term { -ks[ii], -vs[ii] } : term { ks[ii], vs[ii] }; 
    int low = t.x.lb(s);
    t.x -= low;
    k -= t.k * low;
    xs.push(t);
  }
  if(k < 0)
    return false;
  
  /*
  if(xs.size() <= 2) {
    vec<int> o_ks; vec<intvar> o_vs;    
    for(term t : xs) {
      o_ks.push(t.k);
      o_vs.push(t.x);
    }
    new lin_le_inc(s, r, o_ks, o_vs, k);
    return true;
  }
  */
  intvar ps = make_ps(s, r,  xs[0], xs[1], k);
  for(int ii = 2; ii < xs.size() -1; ii++) {
    ps = make_ps(s, r, term { 1, ps }, xs[ii], k);
  }
  vec<int> o_ks { 1, xs.last().k };
  vec<intvar> o_xs { ps, xs.last().x };
  return lin_le_inc::post(s, r, o_ks, o_xs, k);
}

// Euclid's algorithm, straight from wikipedia.
int gcd(int a, int b) {
  int t;
  if(b > a)
    std::swap(a, b);
  while(b != 0) {
    t = b;
    b = a % b;
    a = t;
  }
  return a;
}

int elt_gcd(elt* begin, elt* end) {
  int coeff = begin->c;

  for(++begin; begin != end; ++begin) {
    coeff = gcd(coeff, begin->c);
  }
  return coeff;
}

elt linex_decomp_high_base(solver_data* s, elt* begin, elt* end, int lb, int ub) {
  int coeff = elt_gcd(begin, end);

  vec<int> ks;
  vec<intvar> xs;

  intvar z = new_intvar(s, lb, ub);

  ks.push(-1);
  xs.push(z);
  for(; begin != end; ++begin) {
    ks.push(begin->c / coeff);
    xs.push(begin->x);
  }
  lin_le_inc::post(s, at_True, ks, xs, 0);
  return elt(coeff, z);
}

template<int Deg>
elt linex_decomp_high(solver_data* s, elt* low, elt* high, int lb, int ub, vec<elt>& scratch) {
  if(high - low <= Deg) {
    if(high - low == 1)
      return *low;
    return linex_decomp_high_base(s, low, high, lb, ub);
  }
  // Subdivide.
  int b_idx = scratch.size();
  int sz = high - low;
  int block_sz = sz/Deg;
  int excess = sz - Deg * block_sz;

  for(int ii = 0; ii < Deg; ++ii) {
    elt* next = low + block_sz + (excess > 0);
    excess--;

    int range_lb = 0;
    int range_ub = 0;
    for(const elt& e : range(low, next)) {
      range_lb += e.c * e.x.lb(s->ctx());
      range_ub += e.c * e.x.ub(s->ctx());
    }
    scratch.push(linex_decomp_high<Deg>(s, low, next, range_lb, range_ub, scratch));
    low = next;
  }
  elt ret = linex_decomp_high_base(s, scratch.begin() + b_idx, scratch.end(), lb, ub);
  scratch.shrink(scratch.size() - b_idx);
  return ret;
}

template<int Deg>
bool linear_le_decomp(solver_data* s, patom_t r, vec<int>& ks, vec<intvar>& vs, int k) {
  vec<elt> xs;
  k = normalize_linex(s, ks, vs, k, xs);

  /*
  if(xs.size() <= Deg) {
    // We'll renormalize, but whatever.
    return lin_le_inc::post(s, r, ks, vs, k);
  }
  */
  assert(xs.size() >= Deg);

  int lb = 0;
  int ub = 0;
  for(const elt& e : xs) {
    assert(e.c > 0);
    lb += e.c * e.x.lb(s->ctx());
    ub += e.c * e.x.ub(s->ctx());
  }

  // Trivial cases
  if(lb > k)
    return enqueue(*s, ~r, reason());
  if(lb == k) {
    for(const elt& e : xs) {
      if(!add_clause(s, ~r, e.x <= e.x.lb(s->ctx())))
        return false;
    }
  }
  if(ub <= k) {
    return true;
  }

  // Normal case. Basically same as another recursion level.
  vec<elt> scratch;
  elt* low = xs.begin();
  elt* high = xs.end();
  int sz = xs.size();
  int block_sz = sz/Deg;
  int excess = sz - Deg * block_sz;

  vec<int> top_ks;
  vec<intvar> top_xs;

  // If it's already enforced, we can cut down the
  // upper bound.
  if(r.lb(s->ctx()))
    ub = k;
    
  for(int ii = 0; ii < Deg; ++ii) {
    elt* next = low + block_sz + (excess > 0);
    excess--;

    int range_lb = 0;
    int range_ub = 0;
    for(const elt& e : range(low, next)) {
      range_lb += e.c * e.x.lb(s->ctx());
      range_ub += e.c * e.x.ub(s->ctx());
    }
    // elt block = linex_decomp_high<Deg>(s, low, next, range_lb, std::min(ub, range_lb + (ub - lb)), scratch);
    elt block = linex_decomp_high<Deg>(s, low, next, range_lb, range_ub, scratch);
    top_ks.push(block.c);
    top_xs.push(block.x);
    low = next;
  }
  return lin_le_inc::post(s, r, top_ks, top_xs, k);
}

bool linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r) {
  /*
  if(!s->state.is_entailed_l0(r)) {
    GEAS_WARN("Half-reification not yet implemented for linear_le.");
  }
  */
//   new int_linear_le(s, r, ks, vs, k);
#ifndef USE_CHAIN
  // if(vs.size() > 30)
  //  return linear_le_decomp<4>(s, r, ks, vs, k);
  if(vs.size() > 5) {
    normalize_linex_inplace(s, ks, vs, k);
    return lin_le_mtree<int, intvar>::post(s, r, ks, vs, k);
    // return linear_le_decomp<4>(s, r, ks, vs, k);
  }
  else
    return lin_le_inc::post(s, r, ks, vs, k);
#else
  return linear_le_chain(s, r, ks, vs, k);
#endif
}

bool linear_ne(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r) {
  /*
  if(!s->state.is_entailed_l0(r)) {
    // GEAS_WARN("Half-reification not yet implemented for linear_ne.");
    GEAS_WARN("Half-reified linear_ne is a bit of a hack.");
    patom_t a = new_bool(*s);
    patom_t b = new_bool(*s);
    add_clause(s, ~r, a, b);
    new int_linear_le(s, a, ks, vs, k-1);
    vec<int> neg_ks;
    for(int k : ks)
      neg_ks.push(-k);
    new int_linear_le(s, b, neg_ks, vs, -k+1);
  } else {
    new int_linear_ne(s, r, ks, vs, k);
  }
  */
  // new int_linear_ne(s, r, ks, vs, k);
  // return true;
  return int_linear_ne::post(s, r, ks, vs, k);
}

}
