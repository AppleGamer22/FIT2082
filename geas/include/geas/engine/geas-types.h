#ifndef GEAS_TYPES__H
#define GEAS_TYPES__H
#include <stdint.h>
#include <geas/utils/defs.h>
#include <geas/mtl/Vec.h>

namespace geas {

// Exception if posting a propagator fails.
class RootFail { };

enum Priority { PRIO_HIGH = 0, PRIO_MED = 1, PRIO_LOW = 2, PRIO_LAST = 3, PRIO_LEVELS = 4 };

class lbool {
  lbool(int _x) : x(_x) { }
public:
  static lbool of_int(int x) { return lbool(x); }

  lbool(void) : x(0) { }
  lbool(bool b) : x(b ? 1 : -1) { }

  lbool operator==(const lbool& o) const { return x == o.x; }
  lbool operator!=(const lbool& o) const { return x != o.x; }
  lbool operator^(bool b) const { return lbool(b ? -x : x); }
  lbool operator~(void) const { return lbool(-x); }
  int to_int(void) const { return x; }

  char x;
};

static const lbool l_False = lbool::of_int(-1);
static const lbool l_Undef = lbool::of_int(0);
static const lbool l_True = lbool::of_int(1);

// Atomic predicate values are mapped onto [0, UINT64_MAX-1]
// However, atoms can range from [0, UINT64_MAX].
// Otherwise, ~[|x >= 0|] is not representable.
#ifdef PVAL_32
typedef uint32_t pval_t;
typedef int32_t spval_t;
static const pval_t pval_max = UINT32_MAX-2;
static const pval_t pval_err = UINT32_MAX-1;
static const pval_t pval_min = 0;
#else
typedef uint64_t pval_t;
typedef int64_t spval_t;
static const pval_t pval_max = UINT64_MAX-2;
static const pval_t pval_err = UINT64_MAX-1;
static const pval_t pval_min = 0;
#endif

typedef uint32_t pid_t;

typedef vec<pval_t> ctx_t;

forceinline inline pval_t pval_inv(pval_t v) { return pval_max - v; }
forceinline inline pval_t pval_contra(pval_t v) { return pval_err - v; }
forceinline inline pval_t pred_val(const ctx_t& ctx, pid_t p) {
  return ctx[p];
}
forceinline inline pval_t pred_lb(const ctx_t& ctx, pid_t p) {
  return ctx[p];
}
forceinline inline pval_t pred_ub(const ctx_t& ctx, pid_t p) {
  return pval_inv(ctx[p^1]);
}
forceinline inline bool pred_fixed(const ctx_t& ctx, pid_t p) {
  return pval_inv(ctx[p]) == ctx[p^1];
}

class patom_t {
public:
  // So it's accessible during debugging
  typedef bool val_t;
  static pval_t val_max;

  patom_t(void) : pid(UINT32_MAX), val(0) { }

  patom_t(pid_t _pid, pval_t _val) : pid(_pid), val(_val) { }

  bool operator==(const patom_t& o) const {
    return pid == o.pid && val == o.val;
  }
  bool operator!=(const patom_t& o) const {
    return pid != o.pid || val != o.val;
  }

  patom_t operator~(void) const {
    // return patom_t(pid^1, pval_inv(val) + 1);
    return patom_t(pid^1, pval_contra(val));
  }

  inline bool lb(const vec<pval_t>& ctx) const {
    return ctx[pid] >= val;
  }
  inline bool ub(const vec<pval_t>& ctx) const {
    return ctx[pid^1] < pval_contra(val);
  }

  pid_t pid;
  pval_t val;
};

static const pid_t pid_None = UINT32_MAX;
static const patom_t at_Undef = patom_t(UINT32_MAX, 0);
static const patom_t at_Error = patom_t(UINT32_MAX, pval_err);
static const patom_t at_True = patom_t(0, 0);
static const patom_t at_False = ~at_True;

inline patom_t ge_atom(pid_t p, pval_t v) { return patom_t(p, v); }
inline patom_t le_atom(pid_t p, pval_t v) { return ~patom_t(p, v+1); }

// Event callbacks
enum watch_result { Wt_Keep, Wt_Drop };

class watch_callback {
public:
  typedef watch_result (*fun)(void*, int);

  watch_callback(fun _f, void* _obj, int _data, bool _is_idem = false)
    : f(_f), obj(_obj), data(_data), is_idempotent(_is_idem)
  { }

  watch_result operator()(void) { return f(obj, data); }

  forceinline bool can_skip(void* origin) {
    return is_idempotent && origin == obj;
    // return false;
  }
protected:
  fun f;
  void* obj;
  int data;
  bool is_idempotent;
};

// For removal of a specific value.
template<class V>
class val_callback {
public:
  typedef watch_result (*fun)(void*, int, V);

  val_callback(fun _f, void* _obj, int _data, bool _is_idem = false)
    : f(_f), obj(_obj), data(_data), is_idempotent(_is_idem)
  { }

  watch_result operator()(V k) { return f(obj, data, k); }

  forceinline bool can_skip(void* origin) {
    return is_idempotent && origin == obj;
    // return false;
  }
protected:
  fun f;
  void* obj;
  int data;
  bool is_idempotent;
};

// For other events -- on new_pred, solution, branch or conflict.
// GKG: Perhaps pass in the solver_data?
class event_callback {
public:
  typedef void (*fun)(void*);

  event_callback(fun _f, void* _obj)
    : f(_f), obj(_obj)
  { }

  void operator()(void) { f(obj); }

protected:
  fun f;
  void* obj;
};

template<class T>
class evt {
public:
  typedef T E;
  
  template<void (E::*F)(void)>
  static void call_evt(void* ptr) {
    return (static_cast<E*>(ptr)->*F)();
  }

  template<void (E::*F)(void)>
  event_callback event(void) {
    return event_callback(call_evt<F>, (void*) this);
  }
};

inline void run_watches(vec<watch_callback>& watches, void* origin) {
  int jj = 0;
  for(int ii = 0; ii < watches.size(); ii++) {
    watch_callback& cb(watches[ii]);
    if(cb.can_skip(origin) || cb() == Wt_Keep)
    // if(cb() == Wt_Keep)
      watches[jj++] = watches[ii];
  }
  watches.shrink_(watches.size() - jj);
}

inline void run_callbacks(vec<event_callback>& callbacks) {
  for(event_callback& call : callbacks)
    call();
}


}
#endif
