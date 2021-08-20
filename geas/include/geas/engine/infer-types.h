#ifndef GEAS_INFER_TYPES__H
#define GEAS_INFER_TYPES__H
/* Types for the inference engine */

#include <stdint.h>
#include <vector>
#include <geas/mtl/Vec.h>
#include <geas/mtl/int-triemap.h>

#include <geas/utils/defs.h>
#include <geas/engine/geas-types.h>

// #define DEBUG_CLAUSE
// #define SPARSE_WATCHES

// #define CHECK_EXPLNS
// #define TRACK_ORIGIN

#ifdef CHECK_EXPLNS
#ifndef TRACK_ORIGIN
#define TRACK_ORIGIN
#endif
#endif

namespace geas {

class solver_data;

class watch_node;

class clause_elt {
public:
  clause_elt(patom_t _at)
    : atom(_at)
#ifdef CACHE_WATCH
    , watch(nullptr)
#endif
  { }
#ifdef CACHE_WATCH
  clause_elt(patom_t _at, watch_node* _watch)
    : atom(_at), watch(_watch)
  { }
#endif

  patom_t atom;
  // We cache the appropriate watch-list
#ifdef CACHE_WATCH
  watch_node* watch;
#endif
};

struct clause_extra {
  clause_extra(void)
    : depth(0), one_watch(0), is_learnt(0), act(0)
  {
#ifdef DEBUG_CLAUSE 
    static unsigned int num_clauses = 0;
    clause_id = num_clauses++;
#endif
  }
//  bool is_learnt;
//  int depth;
#ifdef DEBUG_CLAUSE
  unsigned int clause_id;
#endif

  int depth : 30;
  unsigned one_watch : 1;
  unsigned is_learnt : 1;

  double act;
#ifdef PROOF_LOG
  int ident;
#endif
};

class clause {
public:
  // Empty constructor, for temporary explanations
  clause(void) : extra(), sz(0) { }

  // As usual, don't use this directly...
  template<class T> clause(T& elts)
    : extra() {
    sz = 0;
    for(clause_elt e : elts)
      data[sz++] = e;
  }
  
  int size(void) const { return sz; }
  
  clause_elt& operator[](int ii) { return data[ii]; }
  clause_elt* begin(void) { return &(data[0]); }
  clause_elt* end(void) { return &(data[sz]); }
  
  range_t<clause_elt> tail(void) { return range(&data[1], &data[sz]); }

  clause_extra extra;

  int sz;
protected:
  clause_elt data[0];
};

// Use this instead
template<class T>
clause* clause_new(T& elts) {
  void* mem = malloc(sizeof(clause) + sizeof(clause_elt)*elts.size());
  return new (mem) clause(elts);
}

inline clause* alloc_clause_mem(int sz) {
  void* mem = malloc(sizeof(clause) + sizeof(clause_elt)*sz);
  clause* c = new (mem) clause();
  c->sz = sz;
  return c;
}

template<typename... Es>
clause* make_clause(clause_elt e, Es... rest) {
  vec<clause_elt> v;
  v.push(e);
  vec_push(v, rest...);
  return clause_new(v);
}

// If c == NULL, the clause is binary -- e0 is the 'other' literal
class clause_head {
public: 
  clause_head(patom_t _e0)
    : e0(_e0), c(nullptr) { }
  clause_head(patom_t _e0, clause* _c)
    : e0(_e0), c(_c) { }

  patom_t e0; // We can stop if e0 is true.
  clause* c;
};

struct watch_extra {
  watch_extra(void)
    : act(0), refs(0) { }

  double act;
  int refs;
};

// Watches for a given atom.
// Maintains a pointer to the next watch.
class watch_node {
public:
  watch_node(void)
    : succ(nullptr) { }
  // patom_t atom;
#ifdef DEBUG_WMAP
  pval_t curr_val;
#endif
  pval_t succ_val;
  watch_extra extra;
  watch_node* succ;  
  vec<patom_t> bin_ws;
  vec<clause_head> ws;
  vec<watch_callback> callbacks;
};

struct MakeWNode {
  watch_node* operator()(pval_t k) const {
    // Create the first node
    watch_node* w(new watch_node());
    w->succ_val = pval_err;
    w->succ = nullptr;  
    return w;
  }

  watch_node* operator()(watch_node* pred, pval_t k) const {
    watch_node* w(new watch_node());
    w->succ_val = pred->succ_val;
    w->succ = pred->succ;

    pred->succ_val = k;
    pred->succ = w;

    return w;
  }
};

// For a given pid_t, map values to the corresponding
// watches.
#ifndef SPARSE_WATCHES
// typedef std::map<pval_t, watch_node*> watch_map;
typedef uint64_triemap<uint64_t, watch_node*, UIntOps> watch_map;
#else
typedef uint64_triemap<uint64_t, watch_node*, UIntOps> watch_trie;
class watch_map {
private:
  watch_map& operator=(watch_map& o) { return *this; }
  watch_map(watch_map& o)
    : kind(W_EAGER), nodes(nullptr) {
      e.base = 0;
  }

public:
  enum Kind { W_EAGER, W_SPARSE, W_LAZY };   
  enum { EAGER_LIMIT = 10 };

  Kind kind;
  union {
    struct {
      pval_t base;
      unsigned int sz;
    } e;
    struct {
      pval_t base;
      unsigned int sz;
    } s;
    watch_trie l;
  };
  watch_node* nodes;

  watch_map(void)
    : kind(W_LAZY) {
      nodes = nullptr;
      MakeWNode m;
      new (&l) watch_trie;
      l.add(0, m(0));
  }

  watch_map(pval_t lb, pval_t ub)
    : kind(ub - lb < EAGER_LIMIT ? W_EAGER : W_LAZY) {
    if(kind == W_EAGER) {
      unsigned int sz = (ub - lb + 1);
      nodes = (watch_node*) malloc(sizeof(watch_node) * (sz+1));
      e.base = lb;
      e.sz = sz;
      watch_node* n = nodes;
      for(; lb <= ub; ++lb, ++n) {
        new (n) watch_node;
        n->succ_val = lb+1;
        n->succ = n+1;
      }
      new (n) watch_node;
      n->succ_val = pval_err;
      n->succ = nullptr;
    } else {
      nodes = nullptr;
      MakeWNode m;
      new (&l) watch_trie;
      l.add(lb, m(lb));
    }
  }
  
  // PRE: xs is ascending.
  // Drop any nodes which aren't present in xs.
  void migrate_watches(watch_node* dest, watch_node* src) {
    if(dest == src)
      return;
    for(patom_t p : src->bin_ws)
      dest->bin_ws.push(p);
    for(clause_head w : src->ws)
      dest->ws.push(w);
    for(watch_callback c : src->callbacks)
      dest->callbacks.push(c);
    src->bin_ws.clear();
    src->ws.clear();
    src->callbacks.clear();
  }

  void shrink(pid_t p, vec<pval_t>& xs) {
    watch_node* pn(nodes);
    watch_node* en(nodes);

    watch_node* curr(nodes);

    pval_t* px = xs.begin();
    pval_t* ex = xs.end();
    pval_t implied = curr->succ_val-1;
    while(pn != en && px != ex) {
      if(*px + 1 < pn->succ_val) {
        ++px;
      } else if(*px + 1 > pn->succ_val) {
        migrate_watches(curr, pn);
        ++pn; 
      } else {
        migrate_watches(curr, pn); 
        curr->succ_val = pn->succ_val;
        if(implied < *px) // FIXME: May have dupes here.
          curr->bin_ws.push(ge_atom(p, *px));
        ++pn;
        ++px;
        ++curr;
        implied = pn->succ_val;
      }
    }
    s.base = 0;
    s.sz = curr - nodes;
    // Call destructors on anything we'll skip
    for(; curr != en; ++curr)
      curr->~watch_node();
  }

  // FIXME: Given values [x1, ..., x_n], we _actually_ need
  // watches on each xi+1, not xi.
  // We need the p parameter so we know which binary clauses to add.
  void make_sparse(pid_t p, vec<pval_t>& xs) {
    switch(kind) {
      case W_EAGER: 
        // Only sparsify if it's worthwhile.
        if(2 * xs.size() < e.sz) {
          kind = W_SPARSE;
          s = { e.base, e.sz };
          shrink(p, xs);
        }
        break;
      case W_SPARSE:
        // Already sparse; drop any values
        // which are no longer feasible.
        shrink(p, xs);
        break;
      case W_LAZY:
        // Allocate the sparse nodes, then
        // migrate everything from the lazy.
        {
          kind = W_SPARSE;
          unsigned int sz = xs.size();
          nodes = (watch_node*) malloc(sizeof(watch_node) * (sz+1));
          
          watch_node* curr(nodes);
          auto lnode(l.begin());
          for(int ii : irange(xs.size())) {
            new (curr) watch_node;
            curr->succ_val = xs[ii]+1;
            curr->succ = curr+1;
            
            if(ii > 0 && xs[ii] > xs[ii-1]+1) {
              // Non-contiguous.
              curr->bin_ws.push(ge_atom(p, xs[ii]));
            }

            while(lnode != l.end() && (*lnode).key <= xs[ii]) {
              migrate_watches(curr, (*lnode).value);  
              delete (*lnode).value;
              ++lnode;
            }
            ++curr;
          }
          new (curr) watch_node;
          curr->succ_val = pval_err;
          curr->succ = nullptr;

          l.~watch_trie();

          s.base = xs[0];
          s.sz = sz;
        }
        break;
      default:
        GEAS_NEVER;
    }
  }
  watch_map(vec<pval_t>& xs)
    : kind(W_SPARSE) {
    unsigned int sz = xs.size();
    s.sz = sz;

    s.base = xs[0];
    nodes = (watch_node*) malloc(sizeof(watch_node) * (sz+1));
    for(int ii = 1; ii <= sz; ++ii) {
      new (&nodes[ii-1]) watch_node;
      nodes[ii-1].succ_val = xs[ii];
      nodes[ii-1].succ = &nodes[ii];
    }
    new (&nodes[sz]) watch_node;
    nodes[sz].succ_val = pval_err;
    nodes[sz].succ = nullptr;
  }

  watch_map(watch_map&& o)
    : kind(o.kind), nodes(o.nodes) {
      switch(o.kind) {
        case W_EAGER:
          e = o.e;
          o.e.sz = 0;
          break;
        case W_SPARSE:
          s = o.s;
          o.s.sz = 0;
          break;
        case W_LAZY:
          l = std::move(o.l);
          break;
      }
      o.nodes = nullptr;
  }

  watch_map& operator=(watch_map&& o) {
    kind = o.kind;
    nodes = o.nodes; o.nodes = nullptr;
    switch(o.kind) {
      case W_EAGER:
        e = o.e;
        o.e.sz = 0;
        break;
      case W_SPARSE:
        s = o.s;
        o.s.sz = 0;
        break;
      case W_LAZY:
        l = std::move(o.l);
    }
    return *this;
  }

  ~watch_map(void) {

    switch(kind) {
      case W_LAZY:
        l.~watch_trie();
        break;
      case W_EAGER:
        for(watch_node* p = nodes; p != nodes+e.sz; ++p)
          p->~watch_node();
        break;
      case W_SPARSE:
        for(watch_node* p = nodes; p != nodes+s.sz; ++p)
          p->~watch_node();
        break;
      default:
        break;
    }
    if(nodes)
      free(nodes);
  }

  watch_node& find_sparse(pval_t k) {
    if(k <= s.base)
      return nodes[0];

    // FIXME
#if 0
    unsigned int pre = 0;
    unsigned int high = s.sz;

    while(pre < high) {
      unsigned int mid = pre + (high - pre)/2;
      if(nodes[mid].succ_val < k)
        pre = mid+1;
      else if(nodes[mid].succ_val > k)
        high = mid; 
      else
        return nodes[mid+1];
    }
    return nodes[high];
#else
    watch_node* p(nodes);
    while(p->succ_val < k)
      ++p;
    return *(p+1);
#endif
  }

  watch_node* find_lazy(pval_t k) {
    MakeWNode m;
    return l.find_or_add(m, k);
  }
  
  watch_node* get(pval_t k) {
    switch(kind) {
      case W_EAGER:
        {
          unsigned int idx = std::min(k - e.base, (pval_t) e.sz);
          return &(nodes[idx]);
        }
      case W_SPARSE:
        return &(find_sparse(k));
      case W_LAZY:
      default:
        return find_lazy(k);
    }
  }
};
#endif

// One of: a clause, a an atom, or a thunk

struct expl_thunk {
  enum expl_flags { Ex_BTPRED = 1, Ex_BTGEN = 2 };
  typedef void (*fun)(void*, int, pval_t, vec<clause_elt>&); 
  
  void operator()(pval_t val, vec<clause_elt>& ex) {
    f(ptr, data, val, ex);
  }

  template<class T, class F>
  void explain(void* ptr, int d, pval_t v, vec<clause_elt>& elt) {
    return F(static_cast<T*>(ptr), d, v, elt);
  }

  fun f;
  void* ptr;
  int data;

  char flags; // pack flags in ptr?
#ifdef TRACK_ORIGIN
  void* origin;
#endif
};

class reason {
  struct le_info { pid_t p; pval_t offset; };
public:
  enum RKind { R_Clause = 0, R_Atom = 1, R_Thunk = 2, R_LE = 3, R_NIL = 4 };

  reason(void)
    : kind(R_NIL) { }

  reason(patom_t _at)
    : kind(R_Atom), at(_at) { }

  reason(clause* _cl)
    : kind(R_Clause), cl(_cl) { }

  reason(expl_thunk t)
    : kind(R_Thunk), eth(t) { }

  reason(pid_t p, pval_t offset)
    : kind(R_LE), le({p, offset}) { }

  RKind kind; 
  union {
    patom_t at; 
    clause* cl;
    le_info le;
    /* Deal with thunk. */
    expl_thunk eth;
  };
#ifdef PROOF_LOG
  int origin;
#endif
};

// For late initialization of a predicate
class pred_init {
public:
  static void expl_none(void* ptr, int xi, pval_t p, vec<clause_elt>& ex) {
    return;
  }

  typedef pval_t (*fun)(void*, int, vec<pval_t>&);
  typedef void (*final)(solver_data*, void*, int);

  pred_init(fun _f, void* _obj, int _data, expl_thunk _eth, final _fin)
    : f(_f), obj(_obj), data(_data), eth(_eth), fin(_fin)
  { }
  pred_init(void)
    : f(nullptr), obj(nullptr), data(0),
      eth(expl_thunk { expl_none, nullptr, 0 }), fin(nullptr) { }
  
  pval_t operator()(vec<pval_t>& state) {
    assert(f);
    return f(obj, data, state);
  }

  reason expl(void) const { return eth; }

  void finalize(solver_data* s) const { return fin(s, obj, data); }

  operator bool() const { return f; }

protected:
  fun f;
  void* obj;
  int data;

  expl_thunk eth;
  final fin;
};

struct pinit_data { pid_t pi; pred_init init; };


}

#endif
