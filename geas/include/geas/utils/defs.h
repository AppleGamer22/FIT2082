#ifndef GEAS_DEFS__H
#define GEAS_DEFS__H
// Syntactic sugar definitions
#include <cassert>
#include <cstdio>
#include <iostream>
#include <algorithm>

#include <geas/mtl/Vec.h>

#define forceinline __attribute__((always_inline))
// #define forceinline 
// #define INLINE_ATTR __attribute__((noinline))
#define INLINE_ATTR forceinline
#define INLINE_SATTR static INLINE_ATTR

#ifdef LOG_ALL
#ifndef LOG_PROP
#define LOG_PROP
#endif
#ifndef LOG_RESTART
#define LOG_RESTART
#endif
#ifndef LOG_GC
#define LOG_GC
#endif
#endif

#define GEAS_NOT_YET assert(0 && "Not yet implemented.")
#define GEAS_NOT_YET_WARN fprintf(stderr, "WARNING: Incompletely implemented.\n")
#define GEAS_WARN(x) fprintf(stderr, "WARNING: %s\n", (x))
#define GEAS_WARN_ONCE(x) do { \
    static bool first = true; \
    if (first) { first = false; fprintf(stderr, "WARNING: %s\n", (x)); } \
  } while(0)
#define GEAS_ERROR assert(0 && "FAILURE.")
// #define GEAS_NEVER __builtin_unreachable()
#define GEAS_NEVER GEAS_ERROR

template<class T, class U>
void vec_push(vec<T>& vec, U& elt) { vec.push(elt); }

template<class T, class U>
void vec_push(vec<T>& vec, U&& elt) { vec.push(elt); }

template<class T, class U, class... Us>
void vec_push(vec<T>& vec, U&& elt, Us... rest) {
  vec.push(elt);
  vec_push(vec, rest...);
}

template<class T, class U, class... Us>
void vec_push(vec<T>& vec, U& elt, Us... rest) {
  vec.push(elt);
  vec_push(vec, rest...);
}

/*
template<class... Us>
class ArgsLen { };
*/
template<class T, class U>
T* ptr_push(T* p, U& elt) { *p = elt; return ++p; }

template<class T, class U, class... Us>
T* ptr_push(T* p, U& elt, Us... rest) {
  (*p) = elt;
  return ptr_push(++p, rest...);
}

template<class T>
struct range_t {
  range_t(T* pre, T* post) 
    : _pre(pre), _post(post) { }
  
  T* begin(void) const { return _pre; }
  T* end(void) const { return _post; }

  T* _pre;
  T* _post;
};

class irange {
public:
  struct iterator {
    iterator(int _i) : i(_i) { }
    iterator& operator++(void) { ++i; return *this; }
    bool operator!=(const iterator& o) const { return i < o.i; }
    int operator*(void) const { return i; }
    int i;
  };

  irange(int _l, int _u) : l(_l), u(_u) { }
  irange(int _u) : l(0), u(_u) { }
  iterator begin(void) const { return iterator(l); }
  iterator end(void) const { return iterator(u); }

  vec<int> to_vec(void) const {
    auto b(begin());
    auto e(end());
    vec<int> v;
    for(; b != e; ++b)
      v.push(*b);
    return v;
  }
protected:
  int l; int u;
};

template<class T>
struct rev_range_t {
  rev_range_t(T* pre, T* post) 
    : _pre(pre), _post(post) { }
  
  struct iterator {
    iterator(T* _p) : p(_p) { }
    bool operator!=(const iterator& o) const { return p != o.p; }
    iterator& operator++(void) { --p; return *this; }
    T& operator*(void) { return *p; }
    T* p;
  };

  iterator begin(void) const { return iterator(_post-1); }
  iterator end(void) const { return iterator(_pre-1); }

  T* _pre;
  T* _post;
};

template<class T>
class num_range_t {
public:
  struct iterator {
    iterator(T _i) : i(_i) { }
    iterator& operator++(void) { ++i; return *this; }
    bool operator!=(const iterator& o) const { return i != o.i; } 
    T operator*(void) const { return i; }
    T i;
  };

  num_range_t(T _u) : l(T(0)), u(_u) { }
  num_range_t(T _l, T _u) : l(_l), u(_u) { }
  iterator begin(void) { return iterator(l); }
  iterator end(void) { return iterator(u); }
protected:
  T l; T u;
};

template<class T>
num_range_t<T> num_range(T lb, T ub) { return num_range_t<T>(lb, ub); }
template<class T>
num_range_t<T> num_range(T ub) { return num_range_t<T>(ub); }

template<class T>
range_t<T> range(T* start, T* end) {
  return range_t<T>(start, end);
}
template<class T>
rev_range_t<T> rev_range(T* start, T* end) {
  return rev_range_t<T>(start, end);
}

// Printing vectors
template<class T>
std::ostream& operator<<(std::ostream& o, vec<T>& vs) {
  o << "[";
  auto it = vs.begin();
  if(it != vs.end()) {
    o << *it; 
    for(++it; it != vs.end(); ++it)
      o << "; " << *it;
  }
  o << "]";
  return o;
}

template<class T>
void uniq(vec<T>& xs) {
  if(xs.size() == 0)
    return;

  std::sort(xs.begin(), xs.end());
  int jj = 1;
  for(int ii = 1; ii < xs.size(); ii++) {
    if(xs[ii] != xs[ii-1])
      xs[jj++] = xs[ii];
  }
  xs.shrink(xs.size() - jj);
}

// Assumes positive
inline int iceil(int x, int y) { return (x+y-1)/y; }
  
template<class T>
void vec_init(vec<T>& x, int sz, const T& elt) {
  x.clear();
  for(int ii = 0; ii < sz; ++ii)
    x.push(elt);
}

#endif
