#include <cassert>
#include <map>
#include <geas/mtl/Vec.h>
#include <geas/solver/solver_data.h>
#include <geas/constraints/builtins.h>
#include <geas/engine/propagator_ext.h>

namespace geas {

// z >= k + sum_{c_i b_i}.
template<class V, class R>
class bool_lin_ge : public propagator, public prop_inst<bool_lin_ge<V, R> > {
  typedef bool_lin_ge<V, R> P;

public:
  struct term {
    V c; 
    patom_t x;
  };
protected:
  typedef trailed<V> TrV;
  
  
  // Parameters
  patom_t r;
  V c_z;
  R z;
  vec<term> xs; // Sorted by _decreasing_ weight
  V k;
  
  // Persistent state  
  // TrV low;
  V low;
  Tint idx;

  watch_result wake_r(int _r) {
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_z(int _xi) {
    queue_prop();
    return Wt_Keep; 
  }
  watch_result wake_x(int ti) {
    // set(low, low + xs[ti].c);
    trail_change(s->persist, low, low + xs[ti].c);
#if 0
    // Check consistency
    V l(k);
    for(term t : xs) {
      l += t.c * lb(t.x);
    }
    assert(l >= low);
#endif
    queue_prop();
    return Wt_Keep;
  }

  bool check_sat(ctx_t& ctx) {
    V l = k;
    for(term t : xs) { 
      if(t.x.lb(ctx))
        l += t.c;
    }
    return !r.lb(ctx) || z.ub(ctx) >= l;
  }
  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
  
  void ex_z(int _z, pval_t p, vec<clause_elt>& expl) {
#if 0
    V cap = z.lb_of_pval(p);
    // Now collect a sufficient set of terms.
    vec<int> ex_terms;
    int ii = 0;
    for(; ii < xs.size(); ii++) {
      if(lb(xs[ii].x)) {
        ex_terms.push(ii);
        if(cap <= xs[ii].c)
          goto cover_found; 
        else
          cap -= xs[ii].c;
      }
    }
    GEAS_ERROR;
cover_found:
    V slack = xs[ii].c - cap;
    for(int ti : ex_terms) {
      if(xs[ti].c <= slack) {
        slack -= xs[ti].c;
        continue;
      }
      expl.push(~xs[ti].x);
    }
#else
    /* */
    EX_PUSH(expl, ~r);
    V cap(1 + c_z * (z.lb_of_pval(p) - 1) - k);
    for(term t : xs) {
      if(lb(t.x)) {
        expl.push(~t.x);
        if(cap <= t.c)
          return;
        cap -= t.c;
      }
    }
    GEAS_ERROR;
    /* /
    for(term t : xs) {
      if(lb(t.x))
        expl.push(~t.x);
    }
    */
#endif
  }

  void ex_r(int xi, pval_t _p, vec<clause_elt>& expl) {
    EX_PUSH(expl, z > ub(z));
    V cap(c_z * ub(z) - k);
    if(cap < 0)
      return;
    for(term t : xs) {
      if(lb(t.x)) {
        expl.push(~t.x);
        if(cap < t.c)
          return;
        cap -= t.c;
      }
    }
    GEAS_ERROR;
  }

  void ex_x(int xi, pval_t _p, vec<clause_elt>& expl) {
    EX_PUSH(expl, ~r);
    if(c_z * ub(z) < k + xs[xi].c) {
      assert(c_z * iceil(k + xs[xi].c, c_z) >= k + xs[xi].c);
      assert(c_z * (iceil(k + xs[xi].c, c_z)-1) < k + xs[xi].c);
      expl.push(z >= iceil(k + xs[xi].c, c_z));
      return;
    }
#if 0
    V cap = ub(z) - xs[xi].c;
    // Now collect a sufficient set of terms.
    vec<int> ex_terms;
    int ii = 0;
    for(; ii < xs.size(); ii++) {
      if(lb(xs[ii].x)) {
        ex_terms.push(ii);
        if(cap < xs[ii].c)
          goto cover_found; 
        else
          cap -= xs[ii].c;
      }
    }
    GEAS_ERROR;
cover_found:
    V slack = xs[ii].c - cap;
    std::cout << "%% Slack: " << slack << std::endl;
    for(int ti : ex_terms) {
      if(xs[ti].c < slack) {
        slack -= xs[ti].c;
        continue;
      }
      expl.push(~xs[ti].x);
    }
    expl.push(z >= ub(z) + slack);
#else
    expl.push(z > ub(z));
    /* */
    V cap(c_z * ub(z) - k);
    V total(xs[xi].c);
    for(int ii : irange(xs.size())) {
      if(lb(xs[ii].x)) {
        total += xs[ii].c;
        expl.push(~xs[ii].x);
        if(total > cap)
          return;
      }
    }
    GEAS_ERROR;
    /* /
    for(term t : xs) {
      if(lb(t.x))
        expl.push(~t.x);
    }
    */
#endif
  }

public:
  bool_lin_ge(solver_data* s, patom_t _r, V _c_z, R _z, vec<term>& _ts, V _k)
    : propagator(s), r(_r), c_z(_c_z), z(_z), k(_k), low(k), idx(0) {
    // Make sure all coefficients are positive, and remove
    // any fixed values.
    for(term t : _ts) {
      if(!ub(t.x))
        continue;
      if(lb(t.x)) {
        k += t.c;
        continue;
      }
      if(t.c < 0) {
        // Rewrite in terms of ~x.
        k += t.c;
        t = term { -t.c, ~t.x };
      }
      xs.push(t);
    }
    // set(low, k);   
    low = k;

    std::sort(xs.begin(), xs.end(),
      [](const term& t, const term& u) { return t.c > u.c; });
    
    char z_flags = P::Wt_IDEM;
    // z is idempotent unless z.p is also appears in xs.
    for(const term& t : xs) {
      if(t.x.pid == z.p)
        z_flags = 0;
    }

    // Now add attachments.
    z.attach(E_UB, this->template watch<&P::wake_z>(0, z_flags));
    for(int ti : irange(xs.size())) {
      attach(s, xs[ti].x, this->template watch<&P::wake_x>(ti));
    }

    if(lb(r)) {
      if(c_z * lb(z) < k && !set_lb(z, k, reason()))
        throw RootFail();
    } else {
      // This should be safe, if something was propagated from here,
      // r was already fixed.
      attach(s, r, this->template watch<&P::wake_r>(0, P::Wt_IDEM));
    }
  }

  bool propagate(vec<clause_elt>& confl) {
#if 0
    V l(k);
    for(term t : xs) {
      if(lb(t.x))
        l += t.c;
    }
    assert(l == low);
#endif
    if(c_z * ub(z) < low) {
      if(!enqueue(*s, ~r, this->template expl<&P::ex_r>(0, expl_thunk::Ex_BTPRED)))
        return false;
    }
    if(!lb(r))
      return true;

    if(c_z * lb(z) < low) {
      assert(c_z * iceil(low, c_z) >= low);
      assert(c_z * (iceil(low, c_z)-1) < low);
      if(!set_lb(z, iceil(low, c_z), this->template expl<&P::ex_z>(0, expl_thunk::Ex_BTPRED)))
        return false;
    }

    V slack = ub(z) - low;
    int ii = idx;  
    for(; ii < xs.size() && xs[ii].c > slack; ++ii) {
      assert(low + xs[ii].c > ub(z));
      if(!ub(xs[ii].x))
        continue;
      if(!lb(xs[ii].x)) {
        if(!enqueue(*s, ~xs[ii].x, this->template expl<&P::ex_x>(ii, expl_thunk::Ex_BTPRED)))
          return false;
      }
    }
//    if(ii != idx)
//      set(idx, ii);

    return true;
  }
};

struct term {
  int c;
  patom_t x;
};

/*
struct {
  int operator()(const term& a, const term& b) const {
    return a.c > b.c;
  }
} term_lt;
*/

bool atmost_1(solver_data* s, vec<patom_t>& xs, patom_t r) {
  // ps[ii] is the index of the true element.
  pid_t ps = new_pred(*s, 0, xs.size()-1); 
  for(int ii : irange(xs.size())) {
    if(!add_clause(s, ~r, ge_atom(ps, ii), ~xs[ii]))
      return false;
    if(!add_clause(s, ~r, le_atom(ps, ii), ~xs[ii]))
      return false;
  }
  return true;
}

bool atmost_k(solver_data* s, vec<patom_t>& xs, int k, patom_t r) {
  pid_t ps = new_pred(*s, 0, xs.size()-1);
  for(int xi : irange(xs.size())) {
    if(!add_clause(s, ~r, le_atom(ps, xi), ~xs[xi]))
      return false;
  }
  for(int ki = 1; ki < k; ki++) {
    pid_t qs = new_pred(*s, 0, xs.size()-1);
    for(int xi : irange(xs.size())) {
      if(!add_clause(s, ~r, ge_atom(ps, xi), le_atom(qs, xi), ~xs[xi]))
        return false;
    }
    ps = qs;
  }
  for(int xi : irange(xs.size())) {
    if(!add_clause(s, ~r, ge_atom(ps, xi), ~xs[xi]))
      return false;
  }
  return true;
}

int normalize_terms(vec<int>& cs, vec<patom_t>& xs, vec<term>& ts) {
  int shift = 0; 
  for(int ii : irange(cs.size())) {
    if(cs[ii] > 0) {
      ts.push(term { cs[ii], xs[ii] });
    } else if(cs[ii] < 0) {
      // -k b == -k + k (~b)
      ts.push(term { -cs[ii], ~xs[ii] });
      shift -= cs[ii];
    }
  }
  return shift;
}

template<class V, class R>
bool post_bool_lin_ge(solver_data* s, patom_t r, V c_z, R z, vec<V>& cs, vec<patom_t>& xs, V k) {
  vec< typename bool_lin_ge<V, R>::term > ts;
  assert(cs.size() == xs.size());
  for(int ii : irange(xs.size()))
    ts.push(typename bool_lin_ge<V, R>::term { cs[ii], xs[ii] });
  if(c_z < 0)
    return bool_lin_ge<V, R>::post(s, r, -c_z, -z, ts, k);
  else
    return bool_lin_ge<V, R>::post(s, r, c_z, z, ts, k);
}
template<class V, class R>
bool post_bool_lin_le(solver_data* s, patom_t r, V c_z, R z, vec<V>& cs, vec<patom_t>& xs, V k) {
  vec< typename bool_lin_ge<V, R>::term > ts;
  assert(cs.size() == xs.size());
  for(int ii : irange(xs.size()))
    ts.push(typename bool_lin_ge<V, R>::term { -cs[ii], xs[ii] });
  if(c_z < 0)
    return bool_lin_ge<V, R>::post(s, r, -c_z, z, ts, -k);
  else
    return bool_lin_ge<V, R>::post(s, r, c_z, -z, ts, -k);
}


bool bool_linear_ge(solver_data* s, patom_t r, int c_z, intvar z, vec<int>& cs, vec<patom_t>& xs, int k) {
  return post_bool_lin_ge(s, r, c_z, z, cs, xs, k);
}
bool bool_linear_ge(solver_data* s, patom_t r, intvar z, vec<int>& cs, vec<patom_t>& xs, int k) {
  return post_bool_lin_ge(s, r, 1, z, cs, xs, k);
}
bool bool_linear_le(solver_data* s, patom_t r, intvar z, vec<int>& cs, vec<patom_t>& xs, int k) {
  return post_bool_lin_le(s, r, 1, z, cs, xs, k);
}

/*
bool bool_linear_le(solver_data* s, vec<int>& cs, vec<patom_t>& xs, int k, patom_t r) {
  // Normalize coefficients to positive
  vec<term> ts;
  int shift = normalize_terms(cs, xs, ts);
  k += shift;
  
  // Sort by coefficients
  std::sort(ts.begin(), ts.end(), term_lt);
  assert(k >= 0);
    
  // No half reification?
  assert(s->state.is_entailed(r));

  // Waste to use intvars -- just preds
  // Offset everything by k to avoid underflow
  int off = k;
  vec<pid_t> sums;
  for(int ii = 1; ii < xs.size(); ii++) {
    sums.push(new_pred(*s, off, off + k));
  }

  if(!add_clause(s, ~ts[0].x, ge_atom(sums[0], off + ts[0].c))) // Should only fail if ts[0].x && c > k.
    return false;
  for(int ii = 1; ii < xs.size()-1; ii++) {
    if(!pred_le(s, sums[ii-1], sums[ii], 0))
      return false;
    if(!pred_le(s, sums[ii-1], sums[ii], -ts[ii].c, ts[ii].x))
      return false;
  }
  if(!add_clause(s, ~ts.last().x, le_atom(sums.last(), off + k - ts.last().c)))
    return false;

  return true; 
}
*/

bool bool_linear_ne(solver_data* s, vec<int>& ks, vec<patom_t>& xs, int k, patom_t r) {
  assert(0);
  return true;
}

};
