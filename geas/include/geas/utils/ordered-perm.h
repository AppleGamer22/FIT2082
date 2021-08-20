#ifndef GEAS__ORDERED_PERM__H
#define GEAS__ORDERED_PERM__H
#include <geas/solver/solver_data.h>
#include <geas/vars/intvar.h>

// For tracking, say, ordered lists of lower/upper bounds.
// Assumes (anti-)monotone
// Traits requires:
// Var : Type
// Val : Type
// is_increasing : bool
// attach : solver_data -> var_t -> watch_fun -> unit
// eval : solver_data -> var_t -> val_t.
namespace geas {

template<class Traits>
class OrderedPerm {
  typedef typename Traits::Var var_t;
  typedef typename Traits::Val val_t;
  typedef OrderedPerm<Traits> T;

  struct crossref {
    crossref(unsigned int _pos, var_t _v)
      : x(_v), pos(_pos), val(0) { }

    var_t x; 
    unsigned int pos;
    val_t val;
  };

  void rebuild(void) {
    // Fill in the val parameters.
    // fprintf(stderr, "%% Rebuilding\n");
    for(crossref& e : elts)
      e.val = Traits::eval(s, e.x);
    std::sort(perm.begin(), perm.end(), [this](unsigned int p, unsigned int q) { return elts[p].val < elts[q].val; });
    for(int ii : irange(perm.size())) {
      elts[perm[ii]].pos = ii;
    }
  }
  
  void percolate_up(int xi) INLINE_ATTR {
    val_t v(elts[xi].val);
    unsigned int p(elts[xi].pos);
    unsigned int e(elts.size()-1);
    for(; p < e; ++p) {
      unsigned int yi(perm[p+1]);
      if(!(Traits::compare(elts[yi].val, v)))
        break;
      perm[p] = yi;
      elts[yi].pos = p;
    }
    perm[p] = xi;
    elts[xi].pos = p;
  }

  void percolate_down(int xi) INLINE_ATTR {
    val_t v(elts[xi].val);
    unsigned int p(elts[xi].pos);
    for(; p > 0; --p) {
      unsigned int yi(perm[p-1]);
      if(!(Traits::compare(v, elts[yi].val)))
        break;
      perm[p] = yi;
      elts[yi].pos = p;
    }
    perm[p] = xi;
    elts[xi].pos = p;
  }

  /*
  void percolate(int xi) {
    unsigned int p(elts[xi].pos);
    val_t v(elts[xi].val);
    if(Traits::is_increasing) {
      unsigned int e = elts.size()-1;
      for(; p < e; ++p) {
        unsigned int yi(perm[p+1]);
        if(!(Traits::compare(elts[yi].val, v)))
          break;
        perm[p] = yi;
        elts[yi].pos = p;
      }
      perm[p] = xi;
      elts[xi].pos = p;
    } else {
      for(; p > 0; --p) {
        unsigned int yi(perm[p-1]);
        if(!Traits::compare(v, elts[yi].val))
          break;
        perm[p] = yi;
        elts[yi].pos = p;
      }
      perm[p] = xi;
      elts[xi].pos = p;
    }
  }
  */

  static watch_result s_wake(void* p, int xi) {
    return static_cast<T*>(p)->wake(xi);
  }
  watch_result wake(int xi) {
    // If we haven't re-initialised the permutation,
    // don't bother doing anything.
    if(!is_consistent)
      return Wt_Keep;
    // Otherwise, shift xi back to its appropriate location.
    val_t old(elts[xi].val);
    elts[xi].val = Traits::eval(s, elts[xi].x);
    if(Traits::compare(elts[xi].val, old)) {
      percolate_down(xi);
    } else if(Traits::compare(old, elts[xi].val)) {
      percolate_up(xi);
    }
    return Wt_Keep;
  }

public:
  OrderedPerm(solver_data* _s)
    : s(_s), is_consistent(false) { }

  template<class It>
  OrderedPerm(solver_data* _s, It b, It e)
    : s(_s), is_consistent(false) {
    unsigned int ii = 0;
    for(; b != e; ++b, ++ii) {
      Traits::attach(s, *b, watch_callback(s_wake, this, ii));
      perm.push(ii);
      elts.push(crossref(ii, *b));
    }
  }
  void add(var_t& x) {
    unsigned int pi = perm.size();
    perm.push(pi);
    elts.push(crossref(pi, x));
    wake(pi);  
    Traits::attach(s, x, watch_callback(s_wake, this, pi));
  }
  const vec<unsigned int>& get(void) {
    if(!is_consistent) {
      s->persist.bt_flags.push(&is_consistent);
      is_consistent = true;
      rebuild();
    }
    return perm;
  }

  var_t& operator[](unsigned int xi) { return elts[xi].x; }
  const val_t& value(unsigned int xi) const { return elts[xi].val; }
protected:
  solver_data* s;

  vec<unsigned int> perm;
  vec<crossref> elts;
  char is_consistent;
};

template<class V>
struct By_LB {
  typedef V Var;
  typedef typename V::val_t Val;
  enum { is_increasing = true };
  static void attach(solver_data* s, V& x, watch_callback c) { x.attach(s, E_LB, c); }
  static Val eval(solver_data* s, const V& x) { return x.lb(s); }
  static bool compare(Val p, Val q) { return p < q; }
};

template<class V>
struct By_UB {
  typedef V Var;
  typedef typename V::val_t Val;
  enum { is_increasing = false };
  static void attach(solver_data* s, V& x, watch_callback c) { x.attach(s, E_UB, c); }
  static Val eval(solver_data* s, const V& x) { return x.ub(s); }
  static bool compare(Val p, Val q) { return p < q; }
};

template<class V>
struct By_InvUB {
  typedef V Var;
  typedef typename V::val_t Val;
  enum { is_increasing = true };
  static void attach(solver_data* s, V& x, watch_callback c) { x.attach(s, E_UB, c); }
  static Val eval(solver_data* s, const V& x) { return -x.ub(s); }
  static bool compare(Val p, Val q) { return q < p; }
};

}
#endif
