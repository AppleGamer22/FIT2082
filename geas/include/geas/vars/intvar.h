#ifndef GEAS_VAR__H
#define GEAS_VAR__H
#include <unordered_map>
#include <geas/mtl/int-triemap.h>

#include <geas/utils/interval.h>
#include <geas/engine/infer.h>
#include <geas/solver/model.h>
#include <geas/solver/solver_data.h>

namespace geas {

class intvar_manager;

enum intvar_event { E_None = 0, E_LB = 1, E_UB = 2, E_LU = 3, E_FIX = 4 };

enum ivar_kind { IV_EAGER, IV_SPARSE, IV_LAZY };

intvar_manager* get_ivar_man(solver_data* s);

#define IVAR_INV_OFFSET 3

// Extra bookkeeping for intvars
#if 0
struct ivar_emap {
  pval_t base;
  unsigned int sz;
  patom_t* atoms;  

  template<class F>
  patom_t get(F& f, pval_t v) {
    if(v < base) return at_False;
    if(base+sz <= v) return at_False;

    patom_t at(atoms[v - base]);
    if(at.pid == pid_None) {
      at = f(v);
      atoms[v - base].at = at;
    }
    return at;
  }

  bool in_domain(const ctx_t& ctx, pval_t v) {
    if(v < base) return false;
    if(base+sz <= v) return false;

    patom_t at(atoms[v - base]);
    if(at.pid == pid_None)
      return true;
    else
      return at.ub(ctx); 
  }
};

struct ivar_smap {
  struct smap_node { pval_t k; patom_t at; };
  unsigned int sz;
  smap_node* atoms;

  // Tighten the domain of a value.
  bool shrink(solver_data* s, pid_t v, vec<pval_t>& xs) {
    pval_t* px(xs.begin());
    pval_t* ex(xs.end());
    smap_node* pn(atoms);
    smap_node* en(atoms + sz);

    // Find the new first element.
    while(px != ex && pn != en) {
      if(*px < pn->k)
        ++px;
      else if(*px > pn->k)
        ++pn;
      else {
        goto found_min;      
      }
    }
    // If we reach here, the domain is empty.
    return false; 
found_min:
    pval_t prev = pn->v;
    *curr = *pn;
    ++px; ++pn;
    bool skip = false;
    
    while(px != ex && pn != en) {
      if(*px < pn->k) {
        ++px; skip = true;
      } else if(*px > pn->k) {
        ++pn; skip = true;
      } else {
        if(skip) {
          if(!add_clause(*s, le_atom(v, prev), ge_atom(v, *px)))
            return false; 
        }
        ++curr;
        *curr = *pn;
        ++px;
        ++pn;
      }
    }
    if(!enqueue(*s, le_atom(v, curr->k), reason()))
      return false;

    ++curr;
    sz = curr - atoms;
    return true;
  }

  // Doesn't check bounds.
  bool in_domain(const ctx_t& ctx, int k) const {
    // Find the correct index.
    unsigned int low = 0;
    unsigned int high = sz;
    while(low != high) {
      unsigned int mid = low + (high - low)/2;  
      if(atoms[mid].k > k) {
        high = mid;
      } else if (atoms[mid].k < k) {
        low = mid+1;
      } else {
        // Found the location
        patom_t at(atoms[mid].at);
        if(at.pid == pid_None) {
          return true;
        } else {
          return at.ub(ctx);
        }
      }
    }
    return false;
  }
};
#endif

struct ivar_ext {
  // How should missing values be treated?
  enum IV_Kind { IV_Lazy, IV_Strict };
  struct rem_info { val_callback<int64_t> c; int64_t offset; };
  typedef uint64_triemap<uint64_t, patom_t, UIntOps> eqtable_t;

  ivar_ext(solver_data* _s, pid_t _p, int _idx)
    : s(_s), p(_p), idx(_idx), kind(IV_Lazy) { }

  patom_t get_eqatom(pval_t val);
  void make_eager(void);
  bool make_sparse(vec<pval_t>& vs);

  solver_data* s;
  pid_t p;
  int idx;

  IV_Kind kind;

  vec<watch_callback> b_callbacks[2];
  vec<watch_callback> fix_callbacks;
  vec<rem_info> rem_callbacks;

  // std::unordered_map<pval_t, patom_t> eqtable;
  eqtable_t eqtable;
  vec<pval_t> vals;
};

class intvar {
  friend class intvar_manager;

  static const pval_t offset = ((pval_t) INT64_MIN); 
  // static const pval_t offset = ((pval_t) INT32_MIN); 

public:
#ifdef PVAL_32
  typedef int32_t val_t;
#else
  typedef int64_t val_t;
#endif

  static val_t to_int(pval_t v) { return (val_t) (offset + v); }
  static pval_t from_int(val_t v) { return ((pval_t) v) - offset; }

  intvar(pid_t _p, int _off, ivar_ext* _ext)
    : p(_p), off(_off), ext(_ext) { }

  intvar(void)
    : p(0), off(0), ext(nullptr) { }

  intvar(const intvar& o)
    : p(o.p), off(o.off), ext(o.ext) { }

  intvar& operator=(const intvar& o) {
    p = o.p;
    off = o.off;
    ext = o.ext;
    return *this;
  }

  intvar operator-(void) const {
    return intvar(p^1, -off+IVAR_INV_OFFSET, ext);
  }

  intvar operator+(int k) const {
    return intvar(p, off+k, ext);
  }
  intvar operator-(int k) const {
    return intvar(p, off-k, ext);
  }
  intvar& operator+=(int k) { off += k; return *this; }
  intvar& operator-=(int k) { off -= k; return *this; }

  val_t lb(const vec<pval_t>& ctx) const;
  val_t ub(const vec<pval_t>& ctx) const;
  val_t lb_delta(const vec<pval_t>& ctx_new, const vec<pval_t>& ctx_old) const;
  val_t ub_delta(const vec<pval_t>& ctx_new, const vec<pval_t>& ctx_old) const;
  val_t lb(const solver_data* s) const;
  val_t ub(const solver_data* s) const;
  bool in_domain(const ctx_t& ctx, int k) const;
  bool in_domain_exhaustive(const ctx_t& ctx, int k) const;

  bool is_fixed(const vec<pval_t>& ctx) const;
  bool is_fixed(const solver_data*) const;

  /*
  bool set_lb(val_t min, reason r);
  bool set_ub(val_t max, reason r);
  */
  bool enforce_eqatoms_lb(val_t old_lb);
  bool enforce_eqatoms_ub(val_t old_ub);

  void attach(solver_data* s, intvar_event e, watch_callback c);
  void attach(intvar_event e, watch_callback c);
  void attach_rem(val_callback<int64_t> c);

  int dom_sz_approx(ctx_t& ctx) const; // Cheap
  int dom_sz_exact(ctx_t& ctx) const; // Potentially expensive

  // FIXME: Update to deal with sparse
  num_range_t<val_t> domain(const ctx_t& ctx) const {
    return num_range(lb(ctx), ub(ctx)+1);
  }
  num_range_t<val_t> domain(solver_data* s) const;

  val_t model_val(const model& m) const;

  patom_t operator>=(val_t v) const { return patom_t(p, from_int(v-off)); }
  patom_t operator>(val_t v) const { return patom_t(p, from_int(v-off+1)); }
  patom_t operator<=(val_t v) const { return ~patom_t(p, from_int(v-off+1)); }
  patom_t operator<(val_t v) const { return ~patom_t(p, from_int(v-off)); }
  patom_t operator==(val_t v) {
    if(p&1) {
      // CHECK: Do we need to correct for negation here?
      return ext->get_eqatom(pval_inv(from_int(v-off)));
    } else {
      return ext->get_eqatom(from_int(v-off));
    }
  }
  patom_t operator!=(val_t v) {
    if(p&1) {
      return ~ext->get_eqatom(pval_inv(from_int(v-off)));
    } else {
      return ~ext->get_eqatom(from_int(v-off));
    }
  }

  void explain_eq(val_t v, vec<clause_elt>& expl);
  void explain_neq(val_t v, vec<clause_elt>& expl);

  int lb_of_pval(pval_t p) const { return to_int(p)+off; }
  int ub_of_pval(pval_t p) const { return to_int(pval_inv(p))+off; }

  pid_t p;
  val_t off;
  ivar_ext* ext;
};

intvar new_intvar(solver_data* s, intvar::val_t lb, intvar::val_t ub);
intvar permute_intvar(solver_data* s, intvar x, vec<int>& perm);

class intvar_manager {
public:
  typedef intvar::val_t val_t;


  intvar_manager(solver_data* _s);
  ~intvar_manager(void);
  intvar new_var(val_t lb, val_t ub);

  vec<pid_t> var_preds;

  solver_data* s;
  vec<ivar_ext*> var_exts;

  intvar* zero;
};

// inline patom_t intvar_base::operator==(int64_t v) {

inline bool in_domain(const ctx_t& ctx, intvar x, int k) {
  if(x.ub(ctx) < k)
    return false;
  if(x.lb(ctx) > k)
    return false;

  auto it = x.ext->eqtable.find(intvar::from_int(k-x.off));
  if(it == x.ext->eqtable.end())
    return x.ext->kind != ivar_ext::IV_Strict;

  return (*it).value.ub(ctx);
  /*
  if(it != x.ext->eqtable.end()) {
    // If there's an equality atom,
    // could it be true?
    return (*it).value.ub(ctx);
  }

  return true;
  */
}

// Doesn't assume the bounds have been 
inline bool in_domain_exhaustive(const ctx_t& ctx, intvar x, int k) {
  if(x.ub(ctx) < k)
    return false;
  if(x.lb(ctx) > k)
    return false;

  bool seen = false;
  for(auto p : x.ext->eqtable) {
    int p_k = x.lb_of_pval(p.key);
    if(k == p_k) {
      if(!p.value.ub(ctx))
        return false;
      seen = true;
    } else {
      if(p.value.lb(ctx))
        return false;
    }
  }
  return x.ext->kind != ivar_ext::IV_Strict || seen;
  // Iterate through all the eqatoms.
  /*
  auto it = x.ext->eqtable.find(intvar::from_int(k-x.off));
  if(it == x.ext->eqtable.end())
    return x.ext->kind != ivar_ext::IV_Strict;

  return (*it).value.ub(ctx);
  */
  /*
  if(it != x.ext->eqtable.end()) {
    // If there's an equality atom,
    // could it be true?
    return (*it).value.ub(ctx);
  }

  return true;
  */
}

inline bool in_domain(const solver_data* s, intvar x, int k) {
  return in_domain(s->state.p_vals, x, k);
}

template<class T>
// bool intvar_base::make_sparse(vec<T>& vals) {
bool make_sparse(intvar x, vec<T>& vals) {
  vec<pval_t> vs;
  if(x.p&1) {
    for(const T& v : vals)
      vs.push(pval_inv(intvar::from_int(v-x.off)));
  } else {
    for(const T& v : vals)
      vs.push(intvar::from_int(v-x.off));
  }
  return x.ext->make_sparse(vs);
}

inline void intvar::explain_eq(val_t v, vec<clause_elt>& expl) {
  auto it = ext->eqtable.find(intvar::from_int(v-off));
  if(it != ext->eqtable.end()) {
    patom_t at((*it).value);
    if(at.lb(ext->s->state.p_vals)) {
      expl.push(~at);
      return;
    }
  }

  solver_data* s(ext->s);
  // Doesn't already exist.
  if(lb(s->state.p_last) == ub(s->state.p_last)) {
    // If it didn't become fixed this level, create a new atom.
    expl.push((*this) != v);
  } else {
    expl.push((*this) < v);
    expl.push((*this) > v);
  }
}

inline void intvar::explain_neq(val_t v, vec<clause_elt>& expl) {
  auto it = ext->eqtable.find(intvar::from_int(v-off));
  if(it != ext->eqtable.end()) {
    patom_t at((*it).value);
    if(!at.ub(ext->s->state.p_vals)) {
      expl.push(at);
      return;
    }
  }
  // Doesn't already exist; check if
  // we can safely create it.
  solver_data* s(ext->s);
  if(lb(s) > v) {
    if(lb(s->state.p_last) > v) {
      expl.push((*this) == v);
    } else {
      expl.push((*this) <= v);
    }
    // expl.push((*this) <= v);
  } else {
    assert(ub(s) < v);
    if(ub(s->state.p_last) < v) {
      expl.push((*this) == v);
    } else {
      expl.push((*this) >= v);
    }
    // expl.push((*this) >= v);
  }
}

inline void make_eager(intvar x) {
  x.ext->make_eager();
}

inline intvar::val_t to_int(pval_t v) { return intvar::to_int(v); }

inline pval_t from_int(intvar::val_t v) { return intvar::from_int(v); }


inline int_itv var_unsupp(solver_data* s, intvar x) {
  return int_itv { x.ub(s->state.p_root)+1, x.lb(s->state.p_root)-1 };
}
inline int_itv var_range(ctx_t& ctx, intvar x) {
  return int_itv { x.lb(ctx), x.ub(ctx) };
}
inline int_itv var_range(solver_data* s, intvar x) {
  return int_itv { x.lb(s), x.ub(s) };
}

// forceinline
inline intvar::val_t intvar::lb(const vec<pval_t>& ctx) const {
  return to_int(ctx[p]) + off;
}
// forceinline
inline intvar::val_t intvar::ub(const vec<pval_t>& ctx) const {
  return to_int(pval_inv(ctx[p^1])) + off;
}
inline intvar::val_t intvar::lb_delta(const vec<pval_t>& ctx, const vec<pval_t>& old) const {
  return ctx[p] - old[p];
}
inline intvar::val_t intvar::ub_delta(const vec<pval_t>& ctx, const vec<pval_t>& old) const {
  return ctx[p^1] - old[p^1];
}
inline intvar::val_t intvar::lb(const solver_data* s) const { return lb(s->state.p_vals); }
inline intvar::val_t intvar::ub(const solver_data* s) const { return ub(s->state.p_vals); }
inline bool intvar::in_domain(const ctx_t& ctx, int k) const {
  return geas::in_domain(ctx, *this, k);
}
inline bool intvar::in_domain_exhaustive(const ctx_t& ctx, int k) const {
  return geas::in_domain_exhaustive(ctx, *this, k);
}

inline bool intvar::is_fixed(const vec<pval_t>& ctx) const {
  return pred_fixed(ctx, p);
}
inline bool intvar::is_fixed(const solver_data* s) const { return is_fixed(s->state.p_vals); }

inline num_range_t<intvar::val_t> intvar::domain(solver_data* s) const { return domain(s->state.p_vals); }

/*
inline intvar::val_t intvar::lb(void) const {
  return to_int(s->state.p_vals[pid]);
}

// forceinline
inline intvar::val_t intvar::ub(void) const {
  return to_int(pval_max - s->state.p_vals[pid^1]);
}
*/

}
#endif
