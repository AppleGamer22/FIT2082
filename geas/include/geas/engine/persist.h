#ifndef GEAS_PERSIST_H
#define GEAS_PERSIST_H

// Data structures for managing trailing and
// restoration (except the implication graph, which
// is dealt with in infer.h
#include <geas/engine/geas-types.h>
#include <geas/engine/infer-types.h>

namespace geas {

class solver_data;

class expl_builder {
public:
  expl_builder(clause* _c)
    : c(_c), hd(&(*c)[1]) { }

  void push(const clause_elt& e) { *hd = e; ++hd; }    
  clause* operator*(void) { c->sz = hd - c->begin(); return c; }

  clause* c;
  clause_elt* hd;
};

class persistence {
public:
  typedef struct {
    pid_t p;
    pval_t v;
//    unsigned int depth;
  } pred_entry;

  typedef struct {
    pid_t p;
    watch_node* node;
  } pwatch_entry;

  typedef struct {
    void* ptr;
    char sz;
    uint64_t val;
  } data_entry;
  
  void new_pred(void) {
    pred_touched.push(false);
    pred_touched.push(false);
  }

  unsigned int level(void) const {
    // All the trail_lims should have the same size
    return pred_ltrail_lim.size();
  }

  void root_simplify(void) {
    for(pid_t p : touched_preds)
      pred_touched[p] = false;
    touched_preds.clear();

    pred_ltrail.clear();
    pred_ltrail_lim.clear();
    data_trail.clear();
    dtrail_lim.clear();
    pwatch_trail.clear();
    pwatch_lim.clear();
  }

  clause* alloc_expl(unsigned int sz) {
    clause* c = alloc_clause_mem(sz);
    expl_trail.push(c);
    return c;
  }

  template<class... Es>
  clause* create_expl(Es... es) {
    clause* c = alloc_expl(1 + sizeof...(es));
    clause_elt* dest = &(*c)[1];
    ptr_push(dest, es...);
    c->sz = 1 + sizeof...(es);
    return c;
  }

  vec<bool> pred_touched;
  vec<pid_t> touched_preds;

  // For restoring predicate states
  // vec<int> bvar_trail;
  // vec<int> bvar_trail_lim;

  vec<pred_entry> pred_ltrail;
  vec<int> pred_ltrail_lim;

  // Temporary explanations
  vec<clause*> expl_trail;
  vec<int> expl_trail_lim;

  // Trail for other data
  vec<data_entry> data_trail;
  vec<int> dtrail_lim;

  // Watch heads
  vec<pwatch_entry> pwatch_trail;
  vec<int> pwatch_lim;

  // Flags to reset at a new decision level
  vec<char*> reset_flags;
  // Flags to reset upon backtracking
  vec<char*> bt_flags;
};

void push_level(solver_data* s);
void pop_level(solver_data* s);
void bt_to_level(solver_data* s, unsigned int l);

// If we need to restore the data-trail for explanation.
// Worth taking care, since we don't normally store intra-level checkpoints.
void bt_data_to_pos(solver_data* s, unsigned int data_pos);
   
// When we backtrack beyond the current point, it will be
// restored to val.
template<class T>
inline void trail_fake(persistence& p, T& elt, T val) {
  static_assert(sizeof(T) == 1 || sizeof(T) == 2 || sizeof(T) == 4 || sizeof(T) == 8,
    "sizeof(T) must be 2^k, k <- [0, 3]");
  persistence::data_entry e = { (void*) &elt, sizeof(T), (uint64_t) val };
  p.data_trail.push(e); 
}

// Save the current value of elt
template<class T>
inline void trail_push(persistence& p, T& elt) {
  static_assert(sizeof(T) == 1 || sizeof(T) == 2 || sizeof(T) == 4 || sizeof(T) == 8,
    "sizeof(T) must be 2^k, k <- [0, 3]");
  persistence::data_entry e = { (void*) &elt, sizeof(T), (uint64_t) elt };
  p.data_trail.push(e); 
}

// Save elt, and update
template<class T>
inline void trail_change(persistence& p, T& elt, T val) {
  trail_push(p, elt);
  elt = val;
}

// Batched version of trail_push -- only trailed
// if flag is unset; flag will be cleared at each decision level.
template<class T>
inline void trail_save(persistence& p, T& elt, char& flag) {
  if(flag)
    return;
  trail_push(p, elt);
  p.reset_flags.push(&flag);
  flag = true;
}

template<class T>
struct trailed {
  trailed(T _x) : x(_x), saved(0) { }

  inline void set(persistence& p, T val) {
    trail_save(p, x, saved);
    x = val;
  }
  
  operator T() const { return x; }

  T x; 
  char saved;
};
typedef trailed<int> Tint;
typedef trailed<unsigned int> Tuint;
typedef trailed<char> Tbool;
typedef trailed<char> Tchar;
typedef trailed<double> Tdouble;
typedef trailed<float> Tfloat;

void check_at_fixpoint(solver_data* s);

}

#endif
