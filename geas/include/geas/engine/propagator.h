#ifndef GEAS_PROPAGATOR__H
#define GEAS_PROPAGATOR__H
#include <geas/engine/infer-types.h>
#include <geas/engine/state.h>
#include <geas/engine/persist.h>

#define TRACK_EXEC_COUNT

namespace geas {
class solver_data;

// Lifting actual function pointers to avoid
// vtable lookups
struct prop_t {
  bool (*propagate)(void* p, vec<clause_elt>& confl);
  bool (*check_sat)(void* p);
  void (*root_simplify)(void* p);
  void (*cleanup)(void* p);

  void* ptr;
};

class propagator {
public: 
  // Return the operator implementations
//  virtual prop_t get(void) = 0;

  propagator(solver_data* _s, char priority = PRIO_HIGH);

  virtual ~propagator(void) { }

  virtual bool propagate(vec<clause_elt>& confl) = 0;
  // virtual bool check_sat(void) { return true; }
  virtual bool check_sat(ctx_t& ctx) { return true; }
  virtual bool check_unsat(ctx_t& ctx) { GEAS_WARN_ONCE("Unimplemented inconsistency checker."); return true; }
  bool check_sat(void);
  virtual void root_simplify(void) { }
  virtual void cleanup(void) { is_queued = false; }

  virtual void report_internal(void) { };
  
  // Convenient syntactic sugar (definitions in propagator_ext.h):
  // For trailing:
  template<class T>
  void set(trailed<T>& x, T k);

  template<class T>
  inline void save(T& t, char& flag);

  // And for variables.
  template<class T> bool is_fixed(const T& v) const;
  template<class T> auto lb(const T& v) const -> decltype(v.lb(((pred_state*) nullptr)->p_vals));
  template<class T> auto ub(const T& v) const -> decltype(v.ub(((pred_state*) nullptr)->p_vals));
  template<class T> auto lb_0(const T& v) const -> decltype(v.lb(((pred_state*) nullptr)->p_root));
  template<class T> auto ub_0(const T& v) const -> decltype(v.ub(((pred_state*) nullptr)->p_root));
  template<class T> auto lb_prev(const T& v) const -> decltype(v.lb(((pred_state*) nullptr)->p_last));
  template<class T> auto ub_prev(const T& v) const -> decltype(v.ub(((pred_state*) nullptr)->p_last));
  /*
  template<class T> typename T::val_t ub(const T& v) const;
  template<class T> typename T::val_t lb_0(const T& v) const;
  template<class T> typename T::val_t ub_0(const T& v) const;
  template<class T> typename T::val_t lb_prev(const T& v) const;
  template<class T> typename T::val_t ub_prev(const T& v) const;
  */
  template<class T> typename T::val_t lb_delta(const T& v) const;
  template<class T> typename T::val_t ub_delta(const T& v) const;
  template<class T> bool in_domain(const T& x, typename T::val_t v) const;
  template<class T, class V> bool set_lb(T& x, V v, reason r);
  template<class T, class V> bool set_ub(T& x, V v, reason r);

  template<class T> bool set_lb_with_eq(T& x, typename T::val_t v, reason r);
  template<class T> bool set_ub_with_eq(T& x, typename T::val_t v, reason r);

  template<class T> void EX_PUSH(T& expl, patom_t at);

  // execute dispatches between the checker (in a
  // half-reified case) and proapagator (when it's
  // active).
  // FIXME: Not yet implemented
  bool execute(vec<clause_elt>& confl);

  void queue_prop(void);

  unsigned char priority;
  bool is_idempotent;
  bool is_queued;
// #ifdef PROOF_LOG
  int cons_id;
// #endif
  int prop_id;
#ifdef TRACK_EXEC_COUNT
  int exec_count;
#endif
protected:
  solver_data* s;
};
#define UPDATE_LB(X, VAL, R) do { \
  if(lb(X) < (VAL)) { if(!set_lb(X, VAL, R)) return false; } \
} while(0)
#define UPDATE_UB(X, VAL, R) do { \
  if((VAL) < ub(X)) { if(!set_ub(X, VAL, R)) return false; } \
} while(0)

#define UPDATE_LB_EX(X, VAL, R) (!(lb(X) < (VAL)) || set_lb(X, VAL, R))
#define UPDATE_UB_EX(X, VAL, R) (!(lb(X) < (VAL)) || set_lb(X, VAL, R))

typedef void (*expl_fun)(void*, int , pval_t, vec<clause_elt>&);

// Each propagator class should be an instance of this.
template<class T>
class prop_inst {
  static inline T* cast(void* ptr) { return static_cast<T*>(ptr); }

  // typedef intvar::val_t val_t;
#ifdef PVAL_32
  typedef int32_t val_t;
#else
  typedef int64_t val_t;
#endif

public:
  enum { Wt_IDEM = 1 };
  typedef T P;

#ifdef PVAL_32
  static inline val_t to_int(pval_t v) { return (((pval_t) INT32_MIN) + v); }
#else
  static inline val_t to_int(pval_t v) { return (((pval_t) INT64_MIN) + v); }
#endif

  static bool propagate(void* ptr) { return cast(ptr)->propagate(); }
  static bool check_sat(void* ptr) { return cast(ptr)->check_sat(); }
  static void root_simplify(void* ptr) { return cast(ptr)->root_simplify(); }
  static void cleanup(void* ptr) { return cast(ptr)->cleanup(); }

  static watch_result wake_default(void* ptr, int dummy) {
    cast(ptr)->queue_prop();
    return Wt_Keep;
  }
  
  // FIXME: Provide a central definition to_int
  template<void (T::*F)(int x, pval_t p, vec<clause_elt>& elt)>
  static void ex(void* ptr, int x, pval_t p, vec<clause_elt>& elt) {
    return (cast(ptr)->*F)(x, p, elt);
  }

  template<void (*F)(T* ptr, int x, vec<clause_elt>& elt)>
  static void ex_nil(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    F(cast(ptr), x, elt);
  }

  template<void (T::*F)(int x, vec<clause_elt>& elt)>
  static void ex_nil(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    return (cast(ptr)->*F)(x, elt);
  }

  /*
  template<void (*F)(T* ptr, int x, val_t val, vec<clause_elt>& elt)>
  static void ex_lb(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    F(cast(ptr), x, to_int(pval), elt);
  }

  template<void (T::*F)(int x, val_t val, vec<clause_elt>& elt)>
  static void ex_lb(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    return (cast(ptr)->*F)(x, to_int(pval), elt);
  }

  template<void (*F)(T* ptr, int x, val_t val, vec<clause_elt>& elt)>
  static void ex_ub(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    F(cast(ptr), x, to_int(pval_max - pval), elt);
  }

  template<void (T::*F)(int x, val_t val, vec<clause_elt>& elt)>
  static void ex_ub(void* ptr, int x, pval_t pval, vec<clause_elt>& elt) {
    (cast(ptr)->*F)(x, to_int(pval_max - pval), elt);
  }
  */

  expl_thunk ex_thunk(expl_fun f, int x, char flags = 0) {
    return expl_thunk { f, this, x, flags
#ifdef TRACK_ORIGIN
      , this
#endif
    };
  }

  template<void (T::*F)(int x, pval_t p, vec<clause_elt>& elt)>
  expl_thunk expl(int x, char flags = 0) {
    return expl_thunk { ex<F>, this, x, flags
#ifdef TRACK_ORIGIN
     , this
#endif
    };
  }

  template<watch_result (T::*F)(int)>
  static watch_result watch_fun(void *ptr, int id) {
    return (cast(ptr)->*F)(id);
  }

  template<class V, watch_result (T::*F)(int, V)>
  static watch_result valwatch_fun(void *ptr, int id, V v) {
    return (cast(ptr)->*F)(id, v);
  }

  template<watch_result (T::*F)(int id)>
  watch_callback watch(int id, char flags = 0) {
    return watch_callback(watch_fun<F>, this, id, flags&Wt_IDEM);
  }

  template<class V, watch_result (T::*F)(int id, V v)>
  val_callback<V> watch_val(int id, char flags = 0) {
    return val_callback<V>(valwatch_fun<V, F>, this, id, flags&Wt_IDEM);
  }

  prop_t get_prop_t(void) {
    return prop_t { propagate, check_sat, root_simplify, cleanup, this }; 
  }

  template<class Solver, class ...Args>
  static bool post(Solver* s, Args&&... args) {
    try {
      new T(s, args...);
      return true;
    } catch(RootFail& e) {
      (void) e;
      s->solver_is_consistent = false;
      return false;
    }
  }
};

/*
template<class T, class E>
struct exfun {
  static void explain(void* p, int data, pval_t val, 
    vec<clause_elt>& expl) {
    E(static_cast<T*>(p), data, val, expl);
  }
};
*/

}
#endif
