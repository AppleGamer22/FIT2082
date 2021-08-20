#include <utility>
#include <algorithm>
#include <climits>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/solver/solver_data.h>
#include <geas/solver/solver_ext.h>
#include <geas/vars/intvar.h>
#include <geas/utils/bitops.h>

#include <geas/utils/interval.h>
#include <geas/mtl/p-sparse-set.h>
#include <geas/mtl/support-list.h>

// #define DEBUG_ELEM

namespace geas {

typedef std::pair<int, int> ipair;

struct sort_occ {
  bool operator()(int xi, int xj) const {
    if(ys[xi] == ys[xj])
      return xi < xj;
    return ys[xi] < ys[xj];
  }
  vec<int>& ys;
};

// Propagator, for when the array of interest is large: we propagate only
// bounds of x.
#define ELEM_DOM_SWAP
class int_elem_dom : public propagator, public prop_inst<int_elem_dom> {
  struct row {
    int val; 
    patom_t at;
    vec<int> occurs; // occurs[0] is the current watch.
#ifndef ELEM_DOM_SWAP
    Tint occ_start;
#endif
  };

  watch_result wake_x(int xi) {
    // Check if ys[xi] has another support
    int ri = vals[xi];
    row& r(rows[ri]);
    assert(r.occurs[0] == xi);
    // for(int jj : irange(1, r.occurs.size())) {
#ifdef ELEM_DOM_SWAP
    int start = 1;
#else
    int start = r.occ_start;
#endif
    for(int jj : irange(start, r.occurs.size())) {
      int xj = r.occurs[jj];
      if(!s->state.is_inconsistent(atoms[xj])) {
        // Appropriate replacement found. Replace this
        // watch.
#ifdef ELEM_DOM_SWAP
        r.occurs[jj] = r.occurs[0];
        r.occurs[0] = xj;
#else
        r.occ_start.set(s->persist, jj);
#endif
        attach(s, ~atoms[xj], watch<&P::wake_x>(xj, Wt_IDEM));
        return Wt_Drop;
      }
    }
    expired_rows.push(ri);
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_z(int ri) {
    expired_rows.push(ri); 
    queue_prop();
    return Wt_Keep;
  }
  
  void ex_z(int ri, pval_t _p, vec<clause_elt>& expl) {
    for(int xi : rows[ri].occurs)
      expl.push(atoms[xi]); 
  }

  void init_rows(intvar z, vec<int>& occ, vec<int>& ys, vec<row>& rows) {
    int z_curr = ys[occ[0]];
#ifdef ELEM_DOM_SWAP
    rows.push({ z_curr, z == z_curr, vec<int>() });
#else
    rows.push({ z_curr, z == z_curr, vec<int>(), 0 });
#endif

    for(int xi : occ) {
      int zval = ys[xi];
      
      if(zval != z_curr) {
#ifdef ELEM_DOM_SWAP
        rows.push({ zval, z == zval, vec<int>() });
#else
        rows.push({ zval, z == zval, vec<int>(), 0 });
#endif
//        rows.push();
//        rows.last().val = zval;
//        rows.last().at = (z == zval);
        z_curr = zval;
      }
      rows.last().occurs.push(xi);
    }
  }
public:  
  int_elem_dom(solver_data* s, intvar _z, vec<int>& _ys, intvar _x)
    : propagator(s), z(_z), x(_x), vals(_ys.size(), 0) {
    // Invert ys to get occurrence lists.
    vec<int> ys(_ys);
    for(int xi : irange(ys.size()))
      atoms.push(x == xi);
    vec<int> occ(irange(ys.size()).to_vec());
    std::sort(occ.begin(), occ.end(), sort_occ { ys });

    // Set up the rows
    init_rows(z, occ, ys, rows); 
    // ...then filter the domain of z... 
    uniq(ys); make_sparse(z, ys);
    // ...and set up the cross-references and watches
    for(int ri : irange(rows.size())) {
      int wx = rows[ri].occurs[0];
      attach(s, ~rows[ri].at, watch<&P::wake_z>(ri, Wt_IDEM));
      attach(s, ~atoms[wx], watch<&P::wake_x>(wx, Wt_IDEM));
      for(int xi : rows[ri].occurs)
        vals[xi] = ri;
    }
  }
  bool propagate(vec<clause_elt>& confl) {
    for(int ri : dying_rows) {
      if(!enqueue(*s, ~rows[ri].at, ex_thunk(ex<&P::ex_z>, ri)))
        return false;
    }

    for(int ri : expired_rows) {
      patom_t r(rows[ri].at);
      for(int xi : rows[ri].occurs) {
        if(!enqueue(*s, ~atoms[xi], r))
          return false;
      }
    }
    dying_rows.clear();
    expired_rows.clear();
    return true;
  }

  void cleanup(void) {
    is_queued = false;
    dying_rows.clear();
    expired_rows.clear();
  }

  intvar z;
  intvar x;

  vec<row> rows; // For each z-val, the corresponding xs.
  vec<int> vals; // For each x, the corresponding row.
  vec<patom_t> atoms; // For each x, the x=k atom.
  
  // Transient state
  vec<int> dying_rows;
  vec<int> expired_rows;
};

using namespace B64;
template<class T>
static T* alloc_words(int sz) {
  T* mem(new T[sz]);
  memset(mem, 0, sizeof(T) * sz);
  return mem;
}

template<class T>
static T* alloc(int sz) {
  return alloc_words<T>(req_words(sz));
}


class int_elem_bv : public propagator, public prop_inst<int_elem_bv> {
  inline static bool in_dom(uint64_t* mem, int val) {
    return mem[block(val)] & bit(val);
  }
  inline void rem(uint64_t* mem, char* saved, int val) {
    trail_save(s->persist, mem[block(val)], saved[block(val)]);
    mem[block(val)] &= ~bit(val);
  }
  watch_result wake_x(int xi) {
    if(!in_dom(idx_dom, xi) || !in_dom(z_dom, idx_row[xi]))
       return Wt_Keep;

    rem(idx_dom, idx_saved, xi);
    int ri = idx_row[xi];
    int b = z_residue[ri];

    // Check whether z still has some support.
    if(! (z_supp[ri][b] & idx_dom[b]) ) {
      z_check[block(ri)] |= bit(ri);
      queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_z(int ri) {
    if(!in_dom(z_dom, ri))
      return Wt_Keep;

    rem(z_dom, z_saved, ri);
    *z_elim_tl = ri;
    ++z_elim_tl;

    queue_prop();
    return Wt_Keep;
  }
  
  void ex_z(int ri, pval_t _p, vec<clause_elt>& expl) {
    // z != ri, because all supports of ri were removed.
    int base(0);
    uint64_t* supp(z_supp[ri]);
    for(int b = 0; b < req_words(idx_sz); ++b, base += 64) {
      Iter_Word(base, supp[b], [this, &expl](int c) {
          EX_PUSH(expl, x == c);
        });
    }
  }

public:  
  int_elem_bv(solver_data* s, intvar _z, vec<int>& ys, intvar _x)
    : propagator(s)
    , idx_sz(ys.size())
    , dom_sz(0)
    , z(_z), x(_x)
    , idx_dom(alloc<uint64_t>(idx_sz))
    , idx_saved(alloc<char>(idx_sz))

    , idx_row(new int[idx_sz])
  {
    // Init all the bookkeeping.
    vec<int> idx_perm;
    for(int ii : irange(idx_sz))
      idx_perm.push(ii);
    std::sort(idx_perm.begin(), idx_perm.end(),
              [&ys](int x, int y) {
                if(ys[x] != ys[y]) return ys[x] < ys[y];
                return x < y;
              });
    // Compute the set of feasible z-values, and the
    // corresponding row IDs.
    vec<int> row_vals;
    int rv = ys[idx_perm[0]];
    uint64_t* r_supp = alloc<uint64_t>(idx_sz);
    r_supp[block(idx_perm[0])] |= bit(idx_perm[0]);
    idx_row[idx_perm[0]] = 0;

    for(int ii : idx_perm.tail()) {
      if(ys[ii] != rv) {
        row_vals.push(rv);
        z_supp.push(r_supp);

        rv = ys[ii];
        r_supp = alloc<uint64_t>(idx_sz);
      }
      r_supp[block(ii)] |= bit(ii);
      idx_row[ii] = row_vals.size();
    }
    row_vals.push(rv);
    z_supp.push(r_supp);

    dom_sz = row_vals.size();
    z_check = alloc<uint64_t>(dom_sz);
    z_elim = new int[dom_sz];
    z_elim_tl = z_elim;

    z_dom = alloc<uint64_t>(dom_sz);
    z_saved = alloc<char>(dom_sz);
    z_residue = alloc_words<int>(dom_sz);
    
    row_val = new int[dom_sz];
    for(int ri : irange(dom_sz))
      row_val[ri] = row_vals[ri];

    make_eager(x);
    make_sparse(z, row_vals);
    
    row_atom = new patom_t[dom_sz];
    for(int ri : irange(dom_sz)) {
      patom_t z_at = (z != row_vals[ri]);
      row_atom[ri] = z_at;
      if(z.in_domain(s->ctx(), row_vals[ri])) {
        z_dom[block(ri)] |= bit(ri);
        attach(s, z_at, watch<&P::wake_z>(ri));
        z_check[block(ri)] |= bit(ri);
      }
    }

    for(int ii : irange(idx_sz)) {
      // Now do some pruning.
      if(!x.in_domain(s->ctx(), ii))
        continue;
      int rv = row_vals[idx_row[ii]];
      if(!z.in_domain(s->ctx(), rv)) {
        if(!enqueue(*s, x != ii, reason()))
          throw RootFail {};
        continue;
      }
      // Otherwise, watch changes to x.
      idx_dom[block(ii)] |= bit(ii);
      attach(s, x != ii, watch<&P::wake_x>(ii));
    }
  }

  bool check_sat(ctx_t& ctx) {
    for(int ii : irange(idx_sz)) {
      if(!x.in_domain_exhaustive(ctx, ii))
        continue;
      int rv = row_val[idx_row[ii]];
      if(!z.in_domain_exhaustive(ctx, rv))
        continue;
      return true;
    }
    return false;
  }

  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
 
  ~int_elem_bv(void) {
    // Delete a billion arrays.
    // TODO: Should really just compute the required size, and allocate that upfront.
    delete[] row_atom;
    delete[] idx_row;
    delete[] row_val;

    delete[] z_dom;
    delete[] idx_dom;
    delete[] z_saved;
    delete[] idx_saved;
    for(uint64_t* s : z_supp)
      delete[] s;
    delete[] z_residue;
    delete[] z_elim;
    delete[] z_check;
  }

  // Check whether a given value has a remaining support.
  inline bool check_row(int ri) {
    uint64_t* r_supp(z_supp[ri]);
    for(int b = 0; b < req_words(idx_sz); ++b) {
      if(r_supp[b] & idx_dom[b]) {
        z_residue[ri] = b;
        return true;
      }
    }
    return false;
  }

  bool propagate(vec<clause_elt>& confl) {
    int base = 0;
    for(int b = 0; b < req_words(dom_sz); ++b, base += 64) {
      bool okay = Forall_Word(base, z_check[b], [this](int ri) {
        if(check_row(ri)) return true;
        if(!enqueue(*s, row_atom[ri], expl<&P::ex_z>(ri)))
          return false;
        rem(z_dom, z_saved, ri);
        return true;
      });
      if(!okay) return false;
    }

    // Zero out any rows corresponding to ri.
    for(int ri : range(z_elim, z_elim_tl)) {
      uint64_t* supp(z_supp[ri]);
      patom_t r(~row_atom[ri]);

      int base = 0;
      for(int b = 0; b < req_words(idx_sz); ++b, base += 64) {
        uint64_t word(idx_dom[b] & supp[b]);
        if(word) {
          if(!Forall_Word(base, word, [this, r](int c) {
                return enqueue(*s, x != c, r);
              }))
            return false;
          // Probably not necessary, so long as idempotence is
          // working.
          trail_save(s->persist, idx_dom[b], idx_saved[b]);
          idx_dom[b] &= ~supp[b];
        }
      }
    }

    return true;
  }

  void cleanup(void) {
    is_queued = false;
    z_elim_tl = z_elim;
    memset(z_check, 0, sizeof(uint64_t) * req_words(dom_sz));
  }

  int dom_sz;
  int idx_sz;

  intvar z;
  intvar x;
 
  patom_t* row_atom; // z_row -> atom
  int* idx_row; // i -> z_row
  int* row_val; // z_row -> int

  // Persistent state
  uint64_t* z_dom;
  uint64_t* idx_dom; // set(i)
  char* z_saved;
  char* idx_saved;
  vec<uint64_t*> z_supp; // z_row -> set(i)

  int* z_residue; // r -> block
  
  // Transient state
  int* z_elim; // Which rows are definitely dead?
  int* z_elim_tl;
  uint64_t* z_check; // Which rows need checking?
};

class int_elem_bnd : public propagator, public prop_inst<int_elem_bnd> {
  static int prop_count;
  enum { C_NONE = 0, C_LB = 1, C_UB = 2, C_LB_ROW = 4, C_UB_ROW = 8 };

  struct row {
    int val; // z-val
    Tint begin;
    Tint end;
    int supp_idx;
    vec<int> occurs; // occurrences
  };

  inline void kill_row(int row) {
    trail_save(s->persist, live_rows.sz, live_saved);
    live_rows.remove(row);
  }

  watch_result wake_x_lb(int _x) {
    if(!(change&C_LB)) {
      change |= C_LB;
      lb_prev = x.lb(s->wake_vals);
      queue_prop();
    }
    return Wt_Keep;
  }
  watch_result wake_x_ub(int _x) {
    if(!(change&C_UB)) {
      change |= C_UB;
      ub_prev = x.ub(s->wake_vals);
      queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_z(int r) {
    // FIXME: Find out why wake_z is called
    // with already-dead rows
    if(live_rows.elem(r)) {
      kill_row(r);
      int l = lb(x);
      if(r == vals[l]) {
        change |= C_LB_ROW;      
        queue_prop();
      }
      int u = ub(x);
      if(r == vals[u]) {
        change |= C_UB_ROW;
        queue_prop();
      }
    }
    return Wt_Keep;
  }

  void ex_z(int ri, pval_t _p, vec<clause_elt>& expl) {
    // z is explained by the gap between consecutive occurrences.
    row& r(rows[ri]);
    if(r.end > 0)
      expl.push(x <= r.occurs[r.end-1]);
    if(r.end < r.occurs.size())
      expl.push(x >= r.occurs[r.end]);
  }

  void ex_x_lb(int live_sz, pval_t p, vec<clause_elt>& expl) {
    int x_lb = x.lb_of_pval(p);

    int x_suff = lb_0(x)-1;
    // For each live row...
    for(int ridx : irange(live_sz)) {
      int ri = live_rows[ridx];
      row& r(rows[ri]);
      // ...find the largest supported value below x_lb.
      int start = 0;
      int end = r.end;
      while(start < end) {
        int mid = start + (end - start)/2;
        if(r.occurs[mid] >= x_lb)
          end = mid;
        else
          start = mid+1;
      }
      if(start > 0 && r.occurs[start-1] > x_suff)
        x_suff = r.occurs[start-1];   
    }

    for(int ridx : irange(live_sz, rows.size())) {
      int ri = live_rows[ridx];
      // Now check which rows need to be included in the explanation.
      // Any rows without occurrences in [x_suff+1, x_lb] can be discarded.
      row& r(rows[ri]);
      int start = 0;
      int end = r.occurs.size();
      while(start < end) {
        int mid = start + (end - start)/2;

        if(r.occurs[mid] > x_lb)
          end = mid;
        else if(r.occurs[mid] < x_suff)
          start = mid+1;
        else {
          // We've found some value inside the forbidden region.
          expl.push(z == r.val);
          break;
        }
      }
    }
    expl.push(x <= x_suff);
  }
   
  void ex_x_ub(int live_sz, pval_t p, vec<clause_elt>& expl) {
    int x_ub = x.ub_of_pval(p);

    int x_suff = ub_0(x)+1;
    // For each live row...
    for(int ridx : irange(live_sz)) {
      int ri = live_rows[ridx];
      row& r(rows[ri]);
      // ...find the largest supported value below x_lb.
      int start = r.begin;
      int end = r.occurs.size();
      while(start < end) {
        int mid = start + (end - start)/2;
        if(r.occurs[mid] <= x_ub)
          start = mid+1;
        else
          end = mid;
      }
      if(start < r.occurs.size() && r.occurs[start] < x_suff)
        x_suff = r.occurs[start];
    }
    assert(x_suff > x_ub);

    for(int ridx : irange(live_sz, rows.size())) {
      int ri = live_rows[ridx];
      // Now check which rows need to be included in the explanation.
      // Any rows without occurrences in [x_suff+1, x_lb] can be discarded.
      row& r(rows[ri]);
      int start = 0;
      int end = r.occurs.size();
      while(start < end) {
        int mid = start + (end - start)/2;

        if(r.occurs[mid] > x_suff)
          end = mid;
        else if(r.occurs[mid] <= x_ub)
          start = mid+1;
        else {
          // We've found some value inside the forbidden region.
          expl.push(z == r.val);
          break;
        }
      }
    }
    expl.push(x >= x_suff);
  }
  
  void init_rows(vec<int>& ys, vec<row>& rows) {
    // Sort occurrences by the corresponding y-value.
    vec<int> occ(irange(ys.size()).to_vec());
    std::sort(occ.begin(), occ.end(), sort_occ {ys});

    int curr_z = ys[occ[0]];
    rows.push(row { curr_z, 0, 0, 0, vec<int>() });
    rows.last().occurs.push(occ[0]);
    for(int ii : irange(1, occ.size())) {
      int yi = occ[ii];
      if(ys[yi] != curr_z) {
        rows.last().end.x = rows.last().occurs.size();

        curr_z = ys[yi];
        rows.push(row { curr_z, 0, 0, 0, vec<int>() });
      }
      rows.last().occurs.push(yi);
    }
    rows.last().end.x = rows.last().occurs.size();
  }

public:
  int_elem_bnd(solver_data *s, patom_t _r, intvar _z, intvar _x, vec<int>& _ys)
    : propagator(s), z(_z), x(_x), vals(_ys.size(), 0),
      live_saved(0),
      change(0) {
    assert(s->state.is_entailed(_r)); // FIXME: Implement half-reified element
    
    // Compute the set of live values, and their occurrences. 
    vec<int> ys(_ys);
    init_rows(ys, rows);
    live_rows.growTo(rows.size()); live_rows.sz = rows.size();

    uniq(ys);
    make_sparse(z, ys);

    // Now set the cross-references
    for(int ri : irange(rows.size())) {
      row& r(rows[ri]);
      for(int xi : r.occurs)
        vals[xi] = ri;
    }

    // And attach the propagator
    x.attach(E_LB, watch<&P::wake_x_lb>(0, Wt_IDEM));
    x.attach(E_UB, watch<&P::wake_x_ub>(0, Wt_IDEM));
    for(int ri : irange(rows.size())) {
      row& r(rows[ri]);
      attach(s, z != r.val, watch<&P::wake_z>(ri, Wt_IDEM));
    }
  }
  
  // Check if the current row is still supported.
  bool update_row(int ri, vec<clause_elt>& confl) {
    row& r(rows[ri]);
    int l = lb(x); int u = ub(x);
    int begin = r.begin;
    int end = r.end;

    int supp = r.occurs[r.supp_idx];
    if(supp < l) {
      begin = r.supp_idx+1;
    } else if(supp > u) {
      end = r.supp_idx;
    } else {
      return true;
    }
    
    while(begin != end) {
      int mid = begin + (end - begin)/2;
      int xval = r.occurs[mid];
      if(xval < l) {
        begin = mid+1;
      } else if(u < xval) {
        end = mid;
      } else {
        r.supp_idx = mid;
        break;
      }
    }
    if(begin != r.begin)
      r.begin.set(s->persist, begin);
    if(end != r.end)
      r.end.set(s->persist, end);

    if(begin == end) {
      if(!enqueue(*s, z != r.val, ex_thunk(ex<&P::ex_z>, ri)))
        return false;
      //live_rows.remove(ri);
      kill_row(ri);
    }
    return true;
  }

  bool propagate(vec<clause_elt>& confl) {
      prop_count++;
    if(change&(C_LB|C_UB)) {
      int l = lb(x); int u = ub(x);
      unsigned int scan_sz = 0;
      if(change&C_LB)
        scan_sz += l - lb_prev;
      if(change&C_UB)
        scan_sz += ub_prev - u;
      if(scan_sz < live_rows.size()) {
        // If the bounds only moved a little,
        // check which 
        if(change&C_LB) {
          for(int k : irange(lb_prev, l)) {
            if(!live_rows.elem(vals[k]))
              continue;
            if(!update_row(vals[k], confl))
              return false;
          }
        }
        if(change&C_UB) {
          for(int k : irange(u+1, ub_prev+1)) {
            if(!live_rows.elem(vals[k]))
              continue;
            if(!update_row(vals[k], confl))
              return false;
          }
        }
      } else {
        // If we've jumped too many values, just
        // iterate over the live rows.
        // for(int ii : irange(live_rows.size())) {
        // Run backwards, because of how p_sparseset removal works.
        for(int ii = live_rows.size()-1; ii >= 0; --ii) {
          if(!update_row(live_rows[ii], confl))
            return false;
        }
      }
    }

    if(change&(C_LB|C_LB_ROW)) {
      int l = x.lb(s); int u = x.ub(s);
      // Walk the lb up to the next supported value
      for(; l <= u; ++l) {
        if(live_rows.elem(vals[l]))
          break;
      }
      if(!set_lb(x, l, ex_thunk(ex<&P::ex_x_lb>, live_rows.sz)))
        return false;
    }
    
    if(change&(C_UB|C_UB_ROW)) {
      int l = x.lb(s); int u = x.ub(s);
      // Walk the ub down to the nearest
      // supported value
      for(; l <= u; --u) {
        if(live_rows.elem(vals[u]))
          break;
      }
      if(!set_ub(x, u, ex_thunk(ex<&P::ex_x_ub>, live_rows.sz)))
        return false;
    }
    return true;
  }

  void cleanup(void) {
    is_queued = false;
    change = C_NONE;
  }

  // Problem specification
  intvar z;
  intvar x;
  vec<row> rows;
  vec<int> vals;

  // Persistent state
  p_sparseset live_rows;
  char live_saved;

  // Transient state
  unsigned char change; 
  // Track which values we
  // need to check.
  int lb_prev;
  int ub_prev;
};

bool int_element(solver_data* s, patom_t r, intvar z, intvar x,
                   vec<int>& ys, int base) {
  // Also set domain of ys.
  vec<int> ys_uniq(ys);
  uniq(ys_uniq);

  if(s->state.is_entailed_l0(r)) {
    if(base > x.lb(s))
      enqueue(*s, x >= base, reason());
    if(base + ys.size() <= x.ub(s))
      enqueue(*s, x <= base + ys.size()-1, reason());
    // z.set_lb(ys_uniq[0], reason()); z.set_ub(ys_uniq.last(), reason());

    if(!make_sparse(z, ys_uniq))
      return false;
  } else {
    if(!add_clause(s, ~r, x >= base))
      return false;
    if(!add_clause(s, ~r, x < base + ys.size()))
      return false;

    vec<clause_elt> ps { ~r };
    for(int y : ys)
      ps.push(z == y);
    if(!add_clause(*s, ps))
      return false;
  }

  for(int ii : irange(ys.size())) {
    if(!add_clause(s, ~r, x != ii + base, z == ys[ii]))
      return false;
  }

  // vec<int> ys_uniq(ys); uniq(ys_uniq);

  for(int yy : ys_uniq) {
    vec<clause_elt> ps { ~r, z != yy };
//    ps.push(z != yy);
    for(int ii : irange(ys.size())) {
      if(ys[ii] == yy) {
        ps.push(x == ii + base);
      }
    }
    if(!add_clause(*s, ps))
      return false;
  }

  return true;
}

class elem_var_bnd : public propagator, public prop_inst<elem_var_bnd> {
  // Wakeup and explanation
  static void ex_naive(elem_var_bnd* p, int yi, vec<clause_elt>& expl) {
    expl.push(p->x < p->x.lb(p->s));
    expl.push(p->x > p->x.ub(p->s));
    expl.push(p->z < p->z.lb(p->s));
    expl.push(p->z > p->z.ub(p->s));
    for(intvar& y : p->ys) {
      expl.push(y < y.lb(p->s));
      expl.push(y > y.ub(p->s));
    }
  }

  void ex_y_lb(int yi, pval_t p, vec<clause_elt>& expl) {
    int lb = ys[yi].lb_of_pval(p);
    // expl.push(x < yi + base);
    // expl.push(x > yi + base);
    x.explain_eq(yi+base, expl);
    expl.push(z < lb);
  }

  void ex_y_ub(int yi, pval_t p, vec<clause_elt>& expl) {
    int ub = ys[yi].ub_of_pval(p);
    // expl.push(x < yi + base);
    // expl.push(x > yi + base);
    x.explain_eq(yi+base, expl);
    expl.push(z > ub);
  }
   
  void ex_x_lb(int vi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x < vi+base);
    push_hints(vi, x.lb_of_pval(p) - base, expl);
  }

  void ex_x_ub(int vi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x > vi+base);
    push_hints(x.ub_of_pval(p)-base+1, vi+1, expl);
  }

  /*
  static void ex_z(void* ptr, int pos, pval_t pval, vec<clause_elt>& expl) {
    GEAS_NOT_YET;
  }
  */
  void ex_z_lb(int _vi, pval_t p, vec<clause_elt>& expl) {
    // fprintf(stderr, "elem_bnd::ex::lb(z)\n");
    intvar::val_t z_lb = z.lb_of_pval(p);

    EX_PUSH(expl, x < lb(x));
    EX_PUSH(expl, x > ub(x));

    intvar::val_t z_step = lb_0(z)-1;
    vec<int> step_idxs;
    for(int yi = lb(x) - base; yi <= ub(x) - base; yi++) {
      if(ub(ys[yi]) < z_lb) {
        z_step = std::max(z_step, ub(ys[yi]));
        step_idxs.push(yi);
      } else
        EX_PUSH(expl, ys[yi] < z_lb);
    }
    /*
    if(z_step > lb_0(z))
      expl.push(z <= z_step);
      */
    if(step_idxs.size() > 0) {
      EX_PUSH(expl, z <= z_step);
      for(int yi : step_idxs) {
        EX_PUSH(expl, ys[yi] > z_step);
      }
    }
  }

  void ex_z_ub(int _vi, pval_t p, vec<clause_elt>& expl) {
    // fprintf(stderr, "elem_bnd::ex::ub(z)\n");
    int z_ub = z.ub_of_pval(p); 

    EX_PUSH(expl, x < lb(x));
    EX_PUSH(expl, x > ub(x));

    intvar::val_t z_step = ub_0(z)+1;
    vec<int> step_idxs;
    for(int yi = lb(x) - base; yi <= ub(x) - base; yi++) {
      if(lb(ys[yi]) > z_ub) {
        z_step = std::min(lb(ys[yi]), z_step);
        step_idxs.push(yi);
      } else
        EX_PUSH(expl, ys[yi] > z_ub);
    }
    if(step_idxs.size() > 0) {
      EX_PUSH(expl, z >= z_step);
      for(int yi : step_idxs)
        EX_PUSH(expl, ys[yi] < z_step);
    }
  }

  void push_hints(int low, int high, vec<clause_elt>& expl) {
    intvar::val_t z_ub = z.ub(s);

    intvar::val_t z_low = lb_0(z);
    intvar::val_t z_high = ub_0(z)+1;

    for(int ii : irange(low, high)) {
      intvar::val_t hint = cut_hint[ii];
      if(z_ub < hint) {
        assert(ys[ii].lb(s) >= hint);
        z_high = std::min(z_high, hint);
        expl.push(ys[ii] < hint);
      } else {
        assert(z.lb(s) >= hint);
        expl.push(ys[ii] >= hint);
        z_low = std::max(z_low, hint);
      }
    }
    expl.push(z < z_low);
    expl.push(z >= z_high);
  }
public:
  elem_var_bnd(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys, int _base, patom_t _r)
    : propagator(_s), base(_base), x(_x), z(_z), ys(_ys), r(_r) {
    x.attach(E_LU, watch_callback(wake_default, this, 0, true));
    z.attach(E_LU, watch_callback(wake_default, this, 0, true));
    for(int ii : irange(ys.size())) {
      ys[ii].attach(E_LU, watch_callback(wake_default, this, ii, true)); 
      cut_hint.push(ys[ii].lb(s));
    }
    // Set initial bounds
    if(base > x.lb(s))
      set_lb(x,base, reason());
    if(base + ys.size() <= x.ub(s))
      set_ub(x,base + ys.size()-1, reason()); 
  }

  void root_simplify(void) {
    
  }

  bool check_sat(ctx_t& ctx) {
    for(int ii : irange(ys.size())) {
#if 1
      if(!x.in_domain_exhaustive(ctx, base + ii))
        continue;
#else
      if(x.lb(ctx) > ii + base || x.ub(ctx) < ii+base)
        continue;
#endif
      if(z.ub(ctx) < ys[ii].lb(ctx))
        continue;
      if(ys[ii].ub(ctx) < z.lb(ctx))
        continue;
      return true;
    }
    return false;
  }

  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
    
   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_bnd]]" << std::endl;
#endif
       
      int_itv z_dom { z.lb(s), z.ub(s) };
      int_itv z_supp { z.ub(s)+1, z.lb(s)-1 };

      // Run forward, to find the lower bound
      int vi = x.lb(s) - base;
      int vend = x.ub(s) + 1 - base;

      for(; vi != vend; ++vi) {
        int_itv y_dom { ys[vi].lb(s), ys[vi].ub(s) };
        int_itv y_supp = z_dom & y_dom;
        if(y_supp.empty()) {
          cut_hint[vi] = std::max(z_dom.lb, y_dom.lb);
        } else {
          z_supp = y_supp;
          break;
        }
      }
      int low = vi;

      if(low + base > x.lb(s)) {
        if(!set_lb_with_eq(x,low + base, expl<&P::ex_x_lb>(lb(x)-base, expl_thunk::Ex_BTPRED)))
          return false;
      }

      int high = vi;
      for(++vi; vi != vend; ++vi) {
        int_itv y_dom { ys[vi].lb(s), ys[vi].ub(s) };
        int_itv y_supp = z_dom & y_dom;
        if(y_supp.empty()) {
          cut_hint[vi] = std::max(z_dom.lb, y_dom.lb);
        } else {
          z_supp |= y_supp;
          high = vi;
        }
      }
      if(high + base < x.ub(s)) {
        if(!set_ub_with_eq(x,high + base, expl<&P::ex_x_ub>(ub(x) - base, expl_thunk::Ex_BTPRED)))
          return false;
      }

      if(z_supp.lb > z.lb(s)) {
        if(!set_lb(z, z_supp.lb, expl<&P::ex_z_lb>(0, expl_thunk::Ex_BTPRED)))
          return false;
      }
      if(z_supp.ub < z.ub(s)) {
        if(!set_ub(z, z_supp.ub, expl<&P::ex_z_ub>(0, expl_thunk::Ex_BTPRED)))
          return false;
      }

      if(low == high) {
        intvar& y = ys[low];
        if(z_supp.lb > y.lb(s)) {
          if(!set_lb(y, z_supp.lb, expl<&P::ex_y_lb>(low, expl_thunk::Ex_BTPRED)))
            return false;
        }
        if(z_supp.ub < y.ub(s)) {
          if(!set_ub(y, z_supp.ub, expl<&P::ex_y_ub>(low, expl_thunk::Ex_BTPRED)))
           return false;
        }
      }

      return true;
    }

    int base;
    intvar x;
    intvar z;
    vec<intvar> ys;

    patom_t r;

    vec<intvar::val_t> cut_hint;
};

// Mixed propagator: domain consistent for x, but bounds-consistent for
// y and z.
#if 0
class elem_var_mix : public propagator, public prop_inst<elem_var_mix> {
  // Wakeup and explanation
  enum Task { Z_LB, Z_UB, Y_LB, Y_UB, SNUFF_LOW, SNUFF_HIGH, NOF_TASKS };

  inline int lub(void) const { return ub(lub_tree.root()); }
  inline int glb(void) const { return lb(glb_tree.root()); }

  watch_result wake_z_lb(int _z) {
    if(lb(z) > lub()) {
      // At least one index will be killed.
      queue_task(SNUFF_LOW);
    }
    return Wt_Keep;
  }
  watch_result wake_z_ub(int _z) {
    if(ub(z) < glb()) {
      // Some index is to be killed.
      queue_task(SNUFF_HIGH);
    }
    return Wt_Keep;
  }

  watch_result wake_y_lb(int yi) {
    if(!live_yi.elem(yi))
      return Wt_Keep;
    if(llb_tree.root() == yi) {
      if(llb_tree.repair_min(s)) {
        queue_task(Z_LB);
      }
    }
    repair_glb(yi);
    if(ub(z) < lb(ys[yi]))
      queue_task(SNUFF_HIGH);
    return Wt_Keep;
  }

  watch_result wake_y_ub(int yi) {
    if(!live_yi.elem(yi))
      return Wt_Keep;
    if(gub_tree.root() == yi) {
      if(gub_tree.repair_min(s)) {
        queue_task(Z_UB);
      }
    }
    repair_lub(yi);
    if(ub(ys[yi]) < lb(z))
      queue_task(SNUFF_LOW);
    return Wt_Keep;
  }

  watch_result wake_x(int _x, int k) {
    if(live_yi.elem(k)) {
      live_yi.remove(k);
      // Repair the trees 
      repair_glb(k);
      repair_lub(k);
      if(llb_tree.root() == k) {
        if(llb_tree.repair_min(s))
          queue_task(Z_LB);
      }
      if(gub_tree.root() == k) {
        if(gub_tree.repair_min(s))
          queue_task(Z_UB);
      }
    }
    return Wt_Keep;
  }

  void ex_y_lb(int yi, pval_t p, vec<clause_elt>& expl) {
    EX_PUSH(expl, x != yi);
    EX_PUSH(expl, z < ys[yi].lb_of_pval(p));
  }
  void ex_y_ub(int yi, pval_t p, vec<clause_elt>& expl) {
    EX_PUSH(expl, x != yi);
    EX_PUSH(expl, z > ys[yi].ub_of_pval(p));
  }

  /*
  void ex_x(int xi, pval_t _p, vec<clause_elt>& expl) {
    if(z.ub(s) < ys[xi].lb(s)) {
      expl.push(z > 
    }
  }
  */


  void cleanup(void) {
    tasks.clear();
    is_queued = false;
  }

  void ex_y_lb(int yi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x != yi + base);
    expl.push(z < ys[yi].lb_of_pval(p));
  }

  void ex_y_ub(int yi, pval_t p, vec<clause_elt>& expl) {
    expl.push(x != yi+base);
    expl.push(z > ys[yi].ub_of_pval(p));
  }
   
  void ex_x(int yi, pval_t _p, vec<clause_elt>& expl) {
    if(ub(z) < supp[yi]) {
      expl.push(ys[yi] < supp[yi]);
      expl.push(z >= supp[yi]);
    } else {
      assert(supp[yi] < lb(z));
      assert(ub(ys[yi]) < lb(z));
      expl.push(ys[yi] > supp[yi]);
      expl.push(z <= supp[yi]);
    }
  }

  void ex_z_lb(int live_end, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t z_lb = z.lb_of_pval(p);

    for(int ii : irange(live_end)) {
      int yi = live_yi[ii];
      expl.push(ys[yi] < z_lb);
    }

    if(live_end == 1) {
      expl.push(x != live_yi[0] + base);
    } else {
      for(int ii : irange(live_end, ys.size())) {
        int yi = live_yi[ii];
        expl.push(x == yi + base);
      }
    }
  }

  void ex_z_ub(int live_end, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t z_ub = z.ub_of_pval(p);

    for(int ii : irange(live_end)) {
      int yi = live_yi[ii];
      expl.push(ys[yi] > z_ub);
    }

    if(live_end == 1) {
      expl.push(x != live_yi[0] + base);
    } else {
      for(int ii : irange(live_end, ys.size())) {
        int yi = live_yi[ii];
        expl.push(x == yi + base);
      }
    }
  }

public:
  elem_var_mix(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys)
    : propagator(_s), x(_x), z(_z), ys(_ys),
      llb_tree(ys.size()), glb_tree(ys.size()),
      lub_tree(ys.size()), gub_tree(ys.size()),
      live_yi(ys.size()) {
    // Set all y-values as feasible
    live_yi.sz = ys.size();

    z.attach(E_LB, watch<&P::wake_z_lb>(0, Wt_IDEM));
    z.attach(E_UB, watch<&P::wake_z_ub>(0, Wt_IDEM));
    
    // Make sure all [x = k]s are available.
    make_eager(x);
    x.attach_rem(watch_val<&P::wake_x>(0, Wt_IDEM));

    // Attach on each of the ys. 
    for(int yi : irange(ys.size())) {
      if(!in_domain(x, yi)) {
        live_yi.remove(yi);
        continue;
      }
      if(ub(ys[yi]) < lb(z) || ub(z) < lb(ys[yi])) {
        if(!enqueue(*s, x != yi, reason()))
          throw RootFail();
        live_yi.remove(yi);
        continue;
      }
      ys[yi].attach(E_LB, watch<&P::wake_y_lb>(yi, Wt_IDEM));
      ys[yi].attach(E_UB, watch<&P::wake_y_ub>(yi, Wt_IDEM));
    }
  }

  void root_simplify(void) { }

   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_mix]]" << std::endl;
#endif

      for(int t : tasks) {
        switch(t) {
          Z_LB:
            {
              int yi = llb_tree.root();
              if(!set_lb(z, lb(ys[yi]), expl<&P::ex_z_lb>(0)))
                return false;
            }
            break;
          Z_UB:
            {
              int yi = gub_tree.root();
              if(!set_ub(z, ub(ys[yi]), expl<&P::ex_z_ub>(0)))
                return false;
            }
            break;
          Y_LB:
            {
              assert(live_yi.size() == 1);
              int yi = live_yi[0];
              if(!set_lb(ys[yi], lb(z), expl<&P::ex_y_lb>(yi)))
                return false;
            }
            break;
          Y_UB:
            {
              assert(live_yi.size() == 1);
              int yi = live_yi[0];
              if(!set_ub(ys[yi], ub(z), expl<&P::ex_y_ub>(yi)))
                return false;
            }
            break;
          SNUFF_LOW:
            { // Kill any indices with ub(y) < lb(z)
              if(!lub_tree.forall_lt([&](int yi) {
                if(!enqueue(*s, x != yi, expl<&P::ex_x_low>(yi)))
                  return false;
                  live_yi.remove(yi);
                }, lb(z)))
                return false;
            }
            break;
          SNUFF_HIGH:
            {
              if(!glb_tree.forall_lt([&](int yi) {
                if(!enqueue(*s, x != yi, expl<&P::ex_x_high>(yi)))
                  return false;
                live_yi.remove(yi);
              }, ub(z)))
                return false;
            }
            break;
          default:
            GEAS_ERROR;
        }
      }
      tasks.clear();

      return true;
   }

    intvar x;
    intvar z;
    vec<intvar> ys;

    struct MinLB {
      int operator()(solver_data* s, int yi) {
        if(!p->live_yi.elem(yi)) return INT_MAX;
        return ys[yi].lb(s);
      }
    };
    struct MinUB {
      int operator()(solver_data* s, int yi) {
        if(!p->live_yi.elem(yi)) return INT_MAX;
        return ys[yi].ub(s);
      }
    };
    struct MaxLB {
      int operator()(solver_data* s, int yi) {
        if(!p->live_yi.elem(yi)) return INT_MAX;
        return -ys[yi].lb(s);
      }
    };
    struct MaxUB {
      int operator()(solver_data* s, int yi) {
        if(!p->live_yi.elem(yi)) return INT_MAX;
        return -ys[yi].ub(s);
      }
    };

    // Track the least LB and greatest UB (of feasible
    // indices), to maintain supports for z bounds...
    weak_min_tree<int, EvalLLB> llb_tree;
    weak_min_tree<int, EvalGUB> gub_tree;

    // ...the next lower/upper bound thresholds
    // which will cause a variable will be killed...
    min_tree<int, EvalGLB> glb_tree;
    min_tree<int, EvalLUB> lub_tree;
    // ...and the set of surviving indices
    p_sparseset live_yi;

    // If x=k was removed, what value separated
    // ys[k] from z?
    vec<intvar::val_t> sep; 
};
#endif

inline int get_dom_min(solver_data* s, const vec<intvar>& xs) {
  int low(xs[0].lb(s));
  for(const intvar& x : range(xs.begin()+1, xs.end()))
    low = std::min(low, (int) x.lb(s));
  return low;
}
inline int get_dom_max(solver_data* s, const vec<intvar>& xs) {
  int high(xs[0].ub(s));
  for(const intvar& x : range(xs.begin()+1, xs.end()))
    high = std::max(high, (int) x.ub(s));
  return high;
}

// WARNING: Not safe to add extra [instance]s except at the root node,
// because if the instances array is reallocated, the location of [is_fixed]
// might change.
class elem_var_env : public propagator, public prop_inst<elem_var_env> {
  struct attachment {
    attachment(void) : idx(0), val(0) { }
    attachment(int _idx, int _val) : idx(_idx), val(_val) { }

    int idx : 16;
    int val : 16;
  };

  struct instance {
    void destroy(void) {
      delete[] z_dom;
      delete[] idx_dom;
      delete[] z_dom0;
      delete[] idx_dom0;

      delete[] z_saved;
      delete[] idx_saved;

      delete[] z_dtrail_pos;
      delete[] idx_dtrail_pos;

      delete[] z_supp;
      delete[] idx_supp;
    }

    intvar z;
    intvar idx;

    char is_fixed;
    int fixed_idx;

    uint64_t* z_dom;
    uint64_t* idx_dom;

    uint64_t* z_dom0;
    uint64_t* idx_dom0;
    
    char* z_saved;
    char* idx_saved;

    // When z = c was pruned, what was the data level?
    int* z_dtrail_pos;
    // Equiv for idx.
    int* idx_dtrail_pos;
    
    int* z_supp;
    int* idx_supp;
  };

  inline void save(uint64_t& b, char& flag) {
    if(flag) return;
    trail_push(s->persist, b);
    flag = 1;
    saved_flags.push(&flag);
  }

  inline void rem(uint64_t* mem, char* saved, int val) {
    save(mem[block(val)], saved[block(val)]);
    mem[block(val)] &= ~bit(val);
  }
  // For instance variables i/z, we don't need intra-level checkpoints,
  // so just use the normal trail-save mechanism.
  inline void inst_rem(uint64_t* mem, char* saved, int val) {
    trail_save(s->persist, mem[block(val)], saved[block(val)]);
    mem[block(val)] &= ~bit(val);
  }

  // Checking supports
  bool _check_val(instance& i, int val) {
    const uint64_t* v_inv(inv_dom[val]);
    for(int b = 0; b < req_words(idx_sz); ++b) {
      if(i.idx_dom[b] & v_inv[b]) {
        i.z_supp[val] = b;
        return true;
      }
    }
    return false;
  }
  inline bool check_val(instance& i, int val) {
    int b = i.z_supp[val];
    if(i.idx_dom[b] & inv_dom[val][b])
      return true;
    return _check_val(i, val);
  }

  bool _check_idx(instance& i, int idx) {
    const uint64_t* x_dom(elt_dom[idx]);
    for(int b = 0; b < req_words(dom_sz); ++b) {
      if(i.z_dom[b] & x_dom[b]) {
        i.idx_supp[idx] = b;
        return true;
      }
    }
    return false;
  }
  inline bool check_idx(instance& i, int idx) {
    int b = i.idx_supp[idx];
    if(i.z_dom[b] & elt_dom[idx][b])
      return true;
    return _check_idx(i, idx);
  }

  inline bool memb(uint64_t* mem, int val) const {
    return mem[block(val)] & bit(val);
  }

  void ex_z(int tag, pval_t _p, vec<clause_elt>& expl) {
    attachment att(cast::conv<attachment>(tag));
    instance& i(instances[att.idx]);

    // Make sure inv_dom is restored to the moment of propagation.
    bt_data_to_pos(s, i.z_dtrail_pos[att.val]);

    uint64_t* v_inv0(inv_dom0[att.val]);
    uint64_t* v_inv(inv_dom[att.val]);

    int base = 0;
    for(int b = 0; b < req_words(idx_sz); ++b, base += 64) {
      uint64_t to_explain(i.idx_dom0[b] & v_inv0[b]);

      // Anything which still supported att.val at propagation time,
      // must have been removed from dom(idx).
      uint64_t by_idx(to_explain & v_inv[b]);
      uint64_t by_val(to_explain & ~v_inv[b]);

      Iter_Word(base, by_idx, [this, &i, &expl](int c) {
          EX_PUSH(expl, i.idx == c);
        });
      Iter_Word(base, by_val, [this, att, &expl](int c) {
          EX_PUSH(expl, ys[c] == low + att.val);
        });
    }
  }

  void ex_idx(int tag, pval_t _p, vec<clause_elt>& expl) {
    attachment att(cast::conv<attachment>(tag));
    instance& i(instances[att.idx]);

    // Make sure inv_dom is restored to the moment of propagation.
    bt_data_to_pos(s, i.idx_dtrail_pos[att.val]);

    uint64_t* x_dom0(elt_dom0[att.val]);
    uint64_t* x_dom(elt_dom[att.val]);

    int base = 0;
    for(int b = 0; b < req_words(dom_sz); ++b, base += 64) {
      uint64_t to_explain(i.z_dom0[b] & x_dom0[b]);

      // Anything which still supported att.val at propagation time,
      // must have been removed from dom(z).
      uint64_t by_z(to_explain & x_dom[b]);
      uint64_t by_val(to_explain & ~x_dom[b]);

      Iter_Word(base, by_z, [this, &i, &expl](int c) {
          EX_PUSH(expl, i.z == low + c);
        });
      Iter_Word(base, by_val, [this, att, &expl](int c) {
          EX_PUSH(expl, ys[att.val] == low + c);
        });
    }
  }

  // Explain why ys[i] cannot take v.
  void ex_rem_x(int tag, pval_t _p, vec<clause_elt>& expl) {
    attachment att(cast::conv<attachment>(tag));
    instance& i(instances[att.idx]);
    EX_PUSH(expl, i.idx != i.fixed_idx);
    EX_PUSH(expl, i.z == low + att.val);
  }

  watch_result wake_z(int tag) {
    attachment att(cast::conv<attachment>(tag));
    instance& i(instances[att.idx]);
    if(! (i.z_dom[block(att.val)] & bit(att.val)) )
      return Wt_Keep;

    inst_rem(i.z_dom, i.z_saved, att.val);

    z_change[block(att.idx)] |= bit(att.idx);

    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_idx(int tag) {
    attachment att(cast::conv<attachment>(tag));
    instance& i(instances[att.idx]);
    // This shouldn't happen if idempotence handling works.
    if(! (i.idx_dom[block(att.val)] & bit(att.val)) )
      return Wt_Keep;

    inst_rem(i.idx_dom, i.idx_saved, att.val);

    idx_change[block(att.idx)] |= bit(att.idx);

    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_rem(int tag) {
    attachment att(cast::conv<attachment>(tag));
    rem(elt_dom[att.idx], elt_saved[att.idx], att.val);
    rem(inv_dom[att.val], inv_saved[att.val], att.idx);
    touched_vars[block(att.idx)] |= bit(att.idx);
    touched_vals[block(att.val)] |= bit(att.val);

    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_fix(int inst_id) {
    instance& i(instances[inst_id]);
    trail_change(s->persist, i.is_fixed, (char) 1);
    i.fixed_idx = i.idx.lb(s);

    z_change[block(inst_id)] |= bit(inst_id);

    queue_prop();
    return Wt_Keep;
  }

  bool check_sat(ctx_t& ctx);
  bool check_unsat(ctx_t& ctx);

public:
  elem_var_env(solver_data* s, vec<intvar>& _ys)
    : propagator(s), idx_sz(_ys.size())
    , dom_sz(get_dom_max(s, _ys) - get_dom_min(s, _ys) + 1)
    , low(get_dom_min(s, _ys))
    , ys(new intvar[idx_sz])
    , elt_dom(new uint64_t*[idx_sz])
    , elt_dom0(new uint64_t*[idx_sz])
    , elt_saved(new char*[idx_sz])
    , inv_dom(new uint64_t*[dom_sz])
    , inv_dom0(new uint64_t*[dom_sz])
    , inv_saved(new char*[dom_sz])
    , touched_vars(alloc<uint64_t>(idx_sz))
    , touched_vals(alloc<uint64_t>(dom_sz))
  {
    int elt_words = idx_sz * req_words(dom_sz);
    uint64_t* elt_mem = alloc_words<uint64_t>(elt_words);
    uint64_t* elt0_mem = alloc_words<uint64_t>(elt_words);
    char* elt_saved_mem = alloc_words<char>(elt_words);

    int inv_words = dom_sz * req_words(idx_sz);
    uint64_t* inv_mem = alloc_words<uint64_t>(inv_words);
    uint64_t* inv0_mem = alloc_words<uint64_t>(inv_words);
    char* inv_saved_mem = alloc_words<char>(inv_words);

    int offset = 0;
    for(int ii = 0; ii < idx_sz; ++ii) {
      elt_dom[ii] = elt_mem + offset;
      elt_dom0[ii] = elt0_mem + offset;
      elt_saved[ii] = elt_saved_mem + offset;
      offset += req_words(dom_sz);

      ys[ii] = _ys[ii];
    }

    offset = 0;
    for(int ii = 0; ii < dom_sz; ++ii) {
      inv_dom[ii] = inv_mem + offset;
      inv_dom0[ii] = inv0_mem + offset;
      inv_saved[ii] = inv_saved_mem + offset;
      offset += req_words(idx_sz);

      int v(low + ii);
      for(int jj = 0; jj < idx_sz; ++jj) {
        if(ys[jj].in_domain(s->ctx(), v)) {
          attach(s, ys[jj] != v,
                 watch<&P::wake_rem>(cast::conv<int>(attachment(jj, ii))));
          elt_dom[jj][block(ii)] |= bit(ii);
          elt_dom0[jj][block(ii)] |= bit(ii);
          inv_dom[ii][block(jj)] |= bit(jj);
          inv_dom0[ii][block(jj)] |= bit(jj);
        }
      }
    }
  }

  bool attach_instance(intvar idx, intvar z) {
    int inst_id(instances.size());
    instance i = {
      z,
      idx,

      0, // is_fixed
      0, // fixed_idx
      
      alloc<uint64_t>(dom_sz), // z_dom
      alloc<uint64_t>(idx_sz), // idx_dom

      alloc<uint64_t>(dom_sz), // z_dom0
      alloc<uint64_t>(idx_sz), // idx_dom0

      alloc<char>(dom_sz), // z_saved
      alloc<char>(idx_sz), // idx_saved

      new int[dom_sz], // z_dtrail_pos
      new int[idx_sz], // idx_dtrail_pos

      new int[dom_sz], // z_supp
      new int[idx_sz] // idx_supp
    };

    make_eager(idx);
    make_eager(z);
    memset(i.z_supp, 0, sizeof(int) * dom_sz);
    memset(i.idx_supp, 0, sizeof(int) * idx_sz);
    
    // Set bounds on idx/z.
    if(idx.lb(s) < 0 && !set_lb(idx, 0, reason()))
      return false;
    if(idx_sz <= idx.ub(s) && !set_ub(idx, idx_sz-1, reason()))
      return false;
    if(z.lb(s) < low && !set_lb(z, low, reason()))
      return false;
    if(low + dom_sz <= z.ub(s) && !set_ub(z, low + dom_sz - 1, reason()))
      return false;

    // TODO: Propagate initial domains of z/idx.
    
    // Now initialize the data-structures.
    for(int ii = 0; ii < idx_sz; ++ii) {
      if(idx.in_domain(s->ctx(), ii)) {
        attach(s, idx != ii, watch<&P::wake_idx>(cast::conv<int>(attachment(inst_id, ii))));
        i.idx_dom[block(ii)] |= bit(ii);
        i.idx_dom0[block(ii)] |= bit(ii);
      }
    }
    idx.attach(E_FIX, watch<&P::wake_fix>(inst_id));

    for(int ii = 0; ii < dom_sz; ++ii) {
      if(z.in_domain(s->ctx(), low + ii)) {
        attach(s, z != low + ii, watch<&P::wake_z>(cast::conv<int>(attachment(inst_id, ii))));
        i.z_dom[block(ii)] |= bit(ii);
        i.z_dom0[block(ii)] |= bit(ii);
      }
    }

    // Make sure the wakeup queues have enough space.
    instances.push(i);
    if(z_change.size() < req_words(instances.size()))
      z_change.push(0);
    if(idx_change.size() < req_words(instances.size()))
      idx_change.push(0);

    z_change[block(inst_id)] |= bit(inst_id);
    idx_change[block(inst_id)] |= bit(inst_id);
    
    return true;
  }

  inline bool _prop_z(int inst_id) {
    int dtrail_pos = s->persist.data_trail.size();
    instance& i(instances[inst_id]);

    if(i.is_fixed) {
     // Propagate onto the index.
      uint64_t* x_dom(elt_dom[i.fixed_idx]);
      char* x_saved(elt_saved[i.fixed_idx]);

      int base = 0;
      for(int b = 0; b < req_words(dom_sz); ++b, base += 64) {
        uint64_t to_rem = x_dom[b] & ~i.z_dom[b];
        if(to_rem) {
          bool okay = Forall_Word(base, to_rem,
                                    [this, inst_id, &i](int c) {
                                      return enqueue(*s, ys[i.fixed_idx] != low + c,
                                                     expl<&P::ex_rem_x>(cast::conv<int>(attachment(inst_id, c))));
                                    });
          if(!okay) return false;
          // This is slightly annoying -- since later propagations might
          // depend on the changes to x_dom, we need to push it
          // even if it's already saved.
          /*
            // FIXME: Skipping for now, wakeup should take care of it
            // next iteration.
          trail_push(s->persist, x_dom[b]);
          if(!x_saved[b]) {
            saved_flags.push(&x_saved[b]);
            x_saved[b] = true;
          }
          x_dom[b] &= i.z_dom[b];
          */
        }
      }
    } else {
      // z has changed, but index is not fixed. In that case, just check all the indices.
      int base = 0;
      for(int b = 0; b < req_words(idx_sz); ++b, base += 64) {
        uint64_t to_check(i.idx_dom[b]);
        uint64_t i_rem(0);
        bool okay = Forall_Word(base, to_check, [this, dtrail_pos, inst_id, &i, &i_rem](int c) {
            // The same thing we do in prop_indices.
            // TODO: Maybe factor it out.
            if(check_idx(i, c))
              return true;
            // Otherwise, we need to propagate.
            i.idx_dtrail_pos[c] = dtrail_pos;
            if(!enqueue(*s, i.idx != c, expl<&P::ex_idx>(cast::conv<int>(attachment(inst_id, c)))))
              return false;
            i_rem |= bit(c);
            return true;
          });
        if(!okay) return false;
        if(i_rem) {
          trail_save(s->persist, i.idx_dom[b], i.idx_saved[b]);
          i.idx_dom[b] &= ~i_rem;
        }
      }
    }
    return true;
  }
  bool prop_z(void) {
    // Look at only the changed instances.
    return Forall_BV(z_change.begin(), z_change.end(),
                     [this](int i) { return _prop_z(i); });
  }

  inline bool _prop_idx(int inst_id) {
    int dtrail_pos = s->persist.data_trail.size();
    instance& i(instances[inst_id]);

    int base = 0;
    for(int b = 0; b < req_words(dom_sz); ++b, base += 64) {
      // We need to check all values in z_dom.
      uint64_t to_check(i.z_dom[b]);
      uint64_t z_rem(0);
      bool okay = Forall_Word(base, to_check,
                              [this, dtrail_pos, inst_id, &i, &z_rem](int c) {
              if(check_val(i, c))
                return true;
              // Otherwise, we need to propagate.
              i.z_dtrail_pos[c] = dtrail_pos;
              if(!enqueue(*s, i.z != low + c, expl<&P::ex_z>(cast::conv<int>(attachment(inst_id, c)))))
                return false;
              z_rem |= bit(c);
              return true;
          });
      if(!okay) return false;
      if(z_rem) {
        trail_save(s->persist, i.z_dom[b], i.z_saved[b]);
        i.z_dom[b] &= ~z_rem;
      }
    }
    return true;
  }
  bool prop_idx(void) {
    return Forall_BV(idx_change.begin(), idx_change.end(),
                     [this](int i) { return _prop_idx(i); });
  }

  bool prop_indices(void) {
    int dtrail_pos = s->persist.data_trail.size();

    // Only look at the touched values; if z has changed,
    // we will have dealt with it in prop_z.
    int base = 0;
    for(int b = 0; b < req_words(idx_sz); ++b, base += 64) {
      if(!touched_vars[b]) continue;

      for(int inst_id : irange(instances.size())) {
        // Now we only care about things that are still in dom(idx).
        instance& i(instances[inst_id]);
        uint64_t to_check(i.idx_dom[b] & touched_vars[b]);
        if(!to_check)
          continue;

        uint64_t i_rem(0);
        bool okay = Forall_Word(base, to_check, [this, dtrail_pos, inst_id, &i, &i_rem](int c) {
            if(check_idx(i, c))
              return true;
            // Otherwise, we need to propagate.
            i.idx_dtrail_pos[c] = dtrail_pos;
            if(!enqueue(*s, i.idx != c, expl<&P::ex_idx>(cast::conv<int>(attachment(inst_id, c)))))
              return false;
            i_rem |= bit(c);
            return true;
          });
        if(!okay) return false;
        if(i_rem) {
          trail_save(s->persist, i.idx_dom[b], i.idx_saved[b]);
          i.idx_dom[b] &= ~i_rem;
        }
      }
    }

    return true;
  }

  bool prop_vars(void) {
    int dtrail_pos = s->persist.data_trail.size();

    int base = 0;
    for(int b = 0; b < req_words(dom_sz); ++b, base += 64) {
      if(!touched_vals[b]) continue;

      for(int inst_id : irange(instances.size())) {
        instance& i(instances[inst_id]);
        uint64_t to_check(i.z_dom[b] & touched_vals[b]);
        if(!to_check) continue;

        uint64_t z_rem(0);
        bool okay = Forall_Word(base, to_check,
                                [this, dtrail_pos, inst_id, &i, &z_rem](int c) {
              if(check_val(i, c))
                return true;
              // Otherwise, we need to propagate.
              i.z_dtrail_pos[c] = dtrail_pos;
              if(!enqueue(*s, i.z != low + c, expl<&P::ex_z>(cast::conv<int>(attachment(inst_id, c)))))
                return false;
              z_rem |= bit(c);
              return true;
          });
        if(!okay) return false;
        // If there was a change, update the domain of z.
        if(z_rem) {
          trail_save(s->persist, i.z_dom[b], i.z_saved[b]);
          i.z_dom[b] &= ~z_rem;
        }
      }
    }
    return true;
  }

  void clear_flags(void) {
    for(char* c : saved_flags)
      *c = 0;
    saved_flags.clear();
  }

  void cleanup(void) {
    clear_flags();
    memset(touched_vars, 0, sizeof(uint64_t) * req_words(idx_sz));
    memset(touched_vals, 0, sizeof(uint64_t) * req_words(dom_sz));
    memset(z_change.begin(), 0, sizeof(uint64_t) * z_change.size());
    memset(idx_change.begin(), 0, sizeof(uint64_t) * idx_change.size());
    is_queued = false;
  }

  bool propagate(vec<clause_elt>& confl) {
    // Iterate over the changed instance-variables.
    // We do prop_z first, because that can filter out some x-variables.
    if(!prop_z() || !prop_idx())
      return false;
    
    // Now we check the consequence of updated x-vars, across
    // all instances.
    if(!prop_indices())
      return false;

    if(!prop_vars())
      return false;

    clear_flags();
    return true;
  }
  
  ~elem_var_env(void) {
    delete[] *elt_dom;
    delete[] *inv_dom;
    delete[] *elt_saved;
    delete[] *inv_saved;

    delete[] elt_dom;
    delete[] inv_dom;
    delete[] elt_saved;
    delete[] inv_saved;

    delete[] touched_vars;
    delete[] touched_vals;

    for(instance& i : instances)
      i.destroy();
  }

  int idx_sz;
  int dom_sz;
  int low;

  intvar* ys;
  vec<instance> instances;

  uint64_t** elt_dom;
  uint64_t** inv_dom;

  uint64_t** elt_dom0;
  uint64_t** inv_dom0;
  
  char** elt_saved;
  char** inv_saved;

  // Transient state, for changes in xs.
  uint64_t* touched_vars;
  uint64_t* touched_vals;
  vec<uint64_t> z_change; // Which instances had changes in z/idx?
  vec<uint64_t> idx_change;

  // We store saved-flags here, instead of in s,
  // because we need to make sure we have access to
  // intra-propagator checkpoints.
  vec<char*> saved_flags;
};

bool elem_var_env::check_sat(ctx_t& ctx) {
  for(const instance& i : instances) {
    // Check for some i in dom(idx), where dom(z) cap dom(x[i]) is nonempty.
    for(int idx : irange(idx_sz)) {
      if(!i.idx.in_domain_exhaustive(ctx, idx))
        continue;

      for(int c = low; c < low + dom_sz; ++c) {
        if(i.z.in_domain_exhaustive(ctx, c)
           && ys[idx].in_domain_exhaustive(ctx, c))
          goto support_found;
      }
    }
    return false;
  support_found:
    continue;
  }
  return true;
}

bool elem_var_env::check_unsat(ctx_t& ctx) {
  return !check_sat(ctx);
}

// Manages instances 
struct elem_env_man : public solver_ext<elem_env_man> {
  struct key {
    int sz;
    intvar* xs;
  };

  struct CmpKey {
    bool operator()(const key& a, const key& b) const {
      if(a.sz != b.sz)
        return false;
      for(int ii = 0; ii < a.sz; ++ii) {
        if(a.xs[ii].p != b.xs[ii].p)
          return false;
        if(a.xs[ii].off != b.xs[ii].off)
          return false;
      }
      return true;
    }
  };
  struct HashKey {
    size_t operator()(const key& a) const {
      unsigned long hash = 5381;
      hash = ((hash<<5) + hash) + a.sz;
      for(int ii = 0; ii < a.sz; ++ii) {
        hash = ((hash<<5) + hash) + a.xs[ii].p;
        hash = ((hash<<5) + hash) + a.xs[ii].off;
      }
      return hash;
    }
  };

  elem_env_man(solver_data* _s) { }

  elem_var_env* find_element(solver_data* s, vec<intvar>& xs) {
    key k = { xs.size(), xs.begin() };
    auto it(map.find(k));
    if(it != map.end())
      return (*it).second;

    // Otherwise, we need to create it.
    elem_var_env* elt = new elem_var_env(s, xs);
    map.insert(std::make_pair(key { xs.size(), elt->ys }, elt));
    return elt;
  }

  std::unordered_map<key, elem_var_env*, HashKey, CmpKey> map;
};
  
class elem_var_dom : public propagator, public prop_inst<elem_var_dom> {
  bool _prop_val(int v);
  inline bool prop_val(int v) {
    if( inv_dom[v][val_residue[v]] & idx_dom[val_residue[v]] )
      return true;
    return _prop_val(v);
  }

  bool _prop_idx(int i);
  bool prop_idx(int i) {
    if( elt_dom[i][idx_residue[i]] & z_dom[idx_residue[i]] )
      return true;
    return _prop_idx(i);
  }

  bool prop_domain(void);

  struct attachment {
    attachment(void) : var(0), val(0) { }
    attachment(int _var, int _val) : var(_var), val(_val) { }
    int var : 16;
    int val : 16;
  };

  inline bool in_dom(uint64_t* d, int v) const { return d[block(v)] & bit(v); }
  inline void rem(uint64_t* dom, char* saved, int v) {
    trail_save(s->persist, dom[block(v)], saved[block(v)]);
    dom[block(v)] &= ~bit(v);
  }

  watch_result wake_elt(int tag) {
    attachment att(cast::conv<attachment>(tag));
    // If this has already been dealt with, skip it.
    if(!in_dom(idx_dom, att.var) || !in_dom(z_dom, att.val))
      return Wt_Keep;

    rem(elt_dom[att.var], elt_saved[att.var], att.val);
    rem(inv_dom[att.val], inv_saved[att.val], att.var);
    touched_vars[block(att.var)] |= bit(att.var);
    touched_vals[block(att.val)] |= bit(att.val);

    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_z(int v) {
    // Value removed from dom(z). Look at all the
    // indices in inv_dom[v].
    rem(z_dom, z_saved, v);

    uint64_t* v_inv(inv_dom[v]);
    for(unsigned b = 0; b < req_words(idx_sz); ++b)
      touched_vars[b] |= v_inv[b] & idx_dom[b];
      
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_idx(int k) {
    rem(idx_dom, idx_saved, k);

    uint64_t* y_dom(elt_dom[k]);
    for(unsigned b = 0; b < req_words(dom_sz); ++b)
      touched_vals[b] |= y_dom[b] & z_dom[b];

    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_fix(int _p) {
    fixed_idx = idx.lb(s);
    trail_change(s->persist, is_fixed, (char) true);

    queue_prop();
    return Wt_Keep;
  }

  // Explain why dom(z) intersect dom(xi) is empty.
  void ex_idx(int i, pval_t _p, vec<clause_elt>& expl) {
    uint64_t* x_dom(elt_dom[i]);
    uint64_t* x_dom0(elt_dom0[i]);

    int base(low);
    for(unsigned b = 0; b < req_words(dom_sz); ++b) {
      uint64_t to_explain(z_dom0[b] & x_dom0[b]);
      // x_dom should be frozen at the moment of removal.
      // So any values still in x_dom must be because of z_dom.

      uint64_t z_rem(to_explain & x_dom[b]);
      uint64_t x_rem(to_explain & ~x_dom[b]);

      Iter_Word(base, z_rem, [this, &expl](int c) {
          EX_PUSH(expl, z == c);
        });
      Iter_Word(base, x_rem, [this, &expl, i](int c) {
          EX_PUSH(expl, ys[i] == c);
        });
      base += 64;
    }
  }

  // Explain why there are no supports remaining for z = v.
  void ex_val(int v, pval_t _p, vec<clause_elt>& expl) {
    uint64_t* v_inv(inv_dom[v]);
    uint64_t* v_inv0(inv_dom0[v]);

    int base(0);
    for(unsigned b = 0; b < req_words(idx_sz); ++b) {
      uint64_t to_explain(idx_dom0[b] & v_inv0[b]);

      // Similar to idx case, we assume inv_dom[v] is
      // frozen as soon as v is removed.
      uint64_t idx_rem(to_explain & v_inv[b]);
      uint64_t v_rem(to_explain & ~v_inv[b]);

      Iter_Word(base, idx_rem, [this, &expl](int i) {
          EX_PUSH(expl, idx == i);
        });
      Iter_Word(base, v_rem, [this, &expl, v](int i) {
          EX_PUSH(expl, ys[i] == low + v);
        });
      base += 64;
    }
  }

  // Explain why ys[i] cannot take v.
  void ex_rem_x(int v, pval_t _p, vec<clause_elt>& expl) {
    EX_PUSH(expl, idx != fixed_idx);
    EX_PUSH(expl, z == v);
  }

public:

  template<class T>
  static T* alloc(int sz) {
    T* mem(new T[req_words(sz)]);
    memset(mem, 0, sizeof(T) * req_words(sz));
    return mem;
  }

  // At this point, we assume _x is 0-indexed.
  elem_var_dom(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys)
    : propagator(_s)
    , z(_z)
    , idx(_x)
    , ys(_ys)
    , low(get_dom_min(s, _ys))
    , dom_sz(get_dom_max(s, _ys) - low + 1)
    , idx_sz(_ys._size())
    , is_fixed(false)
    , fixed_idx(0)

    , z_dom(alloc<uint64_t>(dom_sz))
    , z_dom0(alloc<uint64_t>(dom_sz))
    , z_saved(alloc<char>(dom_sz))

    , idx_dom(alloc<uint64_t>(idx_sz))
    , idx_dom0(alloc<uint64_t>(idx_sz))
    , idx_saved(alloc<char>(idx_sz))

    , val_residue(new int[dom_sz])
    , idx_residue(new int[idx_sz])

    , touched_vars(alloc<uint64_t>(idx_sz))
    , touched_vals(alloc<uint64_t>(dom_sz)) {
    // Initialize the domains.
    memset(val_residue, 0, sizeof(int) * dom_sz);
    memset(idx_residue, 0, sizeof(int) * idx_sz);

    make_eager(z);
    make_eager(idx);

    idx.attach(E_FIX, watch<&P::wake_fix>(0));

    int val = low;
    for(int ii = 0; ii < dom_sz; ++ii, ++val) {
      inv_dom.push(alloc<uint64_t>(idx_sz));
      inv_dom0.push(alloc<uint64_t>(idx_sz));
      inv_saved.push(alloc<char>(idx_sz));

      if(z.in_domain(s->ctx(), val)) {
        z_dom[block(ii)] |= bit(ii);
        z_dom0[block(ii)] |= bit(ii);

        attach(s, z != val, watch<&P::wake_z>(ii));
      }
    }

    // Now create the var domains, and fill
    // in the inverses.
    int yi = 0;
    for(intvar y : ys) {
      make_eager(y);
      uint64_t* y_dom(alloc<uint64_t>(dom_sz));
      uint64_t* y_dom0(alloc<uint64_t>(dom_sz));
      char* y_saved(alloc<char>(dom_sz));

      // no point populating anything, if it's not
      // in dom(x).
      if(idx.in_domain(s->ctx(), yi)) {
        idx_dom[block(yi)] |= bit(yi);
        idx_dom0[block(yi)] |= bit(yi);
        attach(s, idx != yi, watch<&P::wake_idx>(yi));

        for(int k_raw : y.domain(s)) {
          int k = k_raw - low;
          if(!y.in_domain(s->ctx(), k_raw) || !in_dom(z_dom, k)) 
            continue;

          y_dom[block(k)] |= bit(k);
          y_dom0[block(k)] |= bit(k);

          inv_dom[k][block(yi)] |= bit(yi);
          inv_dom0[k][block(yi)] |= bit(yi);

          attach(s, ys[yi] != k_raw,
                 watch<&P::wake_elt>(cast::conv<int>(attachment(yi, k))));
        }
      }

      elt_dom.push(y_dom);
      elt_dom0.push(y_dom0);
      elt_saved.push(y_saved);
      
      ++yi;
    }
  }

  ~elem_var_dom(void) {
    for(uint64_t* d : elt_dom)
      delete[] d;
    for(uint64_t* d : inv_dom)
      delete[] d;
    for(char* s : elt_saved)
      delete[] s;
    for(char* s : inv_saved)
      delete[] s;

    delete[] z_dom;
    delete[] z_dom0;
    delete[] z_saved;

    delete[] idx_dom;
    delete[] idx_dom0;
    delete[] idx_saved;

    delete[] val_residue;
    delete[] idx_residue;

    delete[] touched_vars;
    delete[] touched_vals;
  }
   
  bool check_sat(ctx_t& ctx) {
    for(int ii = 0; ii < ys.size(); ++ii) {
      if(!idx.in_domain_exhaustive(ctx, ii))
        continue;

      for(int val = low; val < low + dom_sz; ++val) {
        if(z.in_domain_exhaustive(ctx, val)
           && ys[ii].in_domain_exhaustive(ctx, val))
          return true;
      }
    }
    return false;
  }
  bool check_unsat(ctx_t& ctx) {
    return !check_sat(ctx);
  }
  
  bool propagate(vec<clause_elt>& confl) {
    if(is_fixed) {
      if(!prop_domain())
        return false;
    } else {
      if(!Forall_BV(touched_vars, touched_vars + req_words(idx_sz),
              [this](int c) {
                  return prop_idx(c);
                  }))
        return false;
    }

    if(!Forall_BV(touched_vals, touched_vals + req_words(dom_sz),
                  [this](int v) {
                    return prop_val(v);
                  }))
      return false;

    return true;
  }
  
  void cleanup(void) {
    is_queued = false;
    memset(touched_vars, 0, sizeof(uint64_t) * req_words(idx_sz));
    memset(touched_vals, 0, sizeof(uint64_t) * req_words(dom_sz));
  }

  // Parameters
  intvar z;
  intvar idx;
  vec<intvar> ys;

  int low;
  int dom_sz;
  int idx_sz;
  
  // Trailed state
  char is_fixed;
  int fixed_idx;
  
  vec<uint64_t*> elt_dom; // i -> dom(x[i])
  vec<uint64_t*> elt_dom0;
  vec<char*> elt_saved;

  vec<uint64_t*> inv_dom; // v -> { i | v \in dom(x[i]) }
  vec<uint64_t*> inv_dom0;
  vec<char*> inv_saved;

  uint64_t* z_dom;
  uint64_t* z_dom0;
  char* z_saved;

  uint64_t* idx_dom;
  uint64_t* idx_dom0;
  char* idx_saved;

  // Helpers
  int* val_residue; // block supporting value v.
  int* idx_residue; // block supporting index i.

  // Transient state
  uint64_t* touched_vars; // Which vars may no longer have a support?
  uint64_t* touched_vals; // Which vals ...
};

// The value supporting x[i] has been eliminated.
bool elem_var_dom::_prop_idx(int i) {
  int base = 0;
  uint64_t* x_dom(elt_dom[i]);
  for(unsigned b = 0; b < req_words(dom_sz); ++b) {
    if(z_dom[b] & x_dom[b]) {
      idx_residue[i] = b;
      return true;
    }
    base += 64;
  }

  // Otherwise, remove i from the domain of idx (shouldn't change dom[z]).
  if(!enqueue(*s, idx != i, expl<&P::ex_idx>(i)))
    return false;
  rem(idx_dom, idx_saved, i);
  return true;
}

// Only need to propagate z -> x. Other side should come
// naturally.
bool elem_var_dom::prop_domain(void) {
  uint64_t* x_dom(elt_dom[fixed_idx]);
  char* x_saved(elt_saved[fixed_idx]);

  int base = low;
  for(unsigned b = 0; b < req_words(dom_sz); ++b) {
    uint64_t word(x_dom[b] & ~z_dom[b]);
    if(word) {
      do {
        int v = base + __builtin_ctzll(word);
        word &= (word-1);
        if(!enqueue(*s, ys[fixed_idx] != v, expl<&P::ex_rem_x>(v)))
            return false;
      } while(word);
      trail_save(s->persist, x_dom[b], x_saved[b]);
      x_dom[b] &= ~z_dom[b];
    }
    base += 64;
  }
  return true;
}

bool elem_var_dom::_prop_val(int v) {
  int base = 0;
  uint64_t* v_inv(inv_dom[v]);
  for(unsigned b = 0; b < req_words(idx_sz); ++b) {
    if(idx_dom[b] & v_inv[b]) {
      val_residue[v] = b;
      return true;
    }
    base += 64;
  }
  if(!enqueue(*s, z != low + v, expl<&P::ex_val>(v)))
    return false;
  rem(z_dom, z_saved, v);
  return true;
}

// Non-incremental interval-based propagation
#if 0
class elem_var_simple : public propagator, public prop_inst<elem_var_simple> {
  // Wakeup and explanation
  static watch_result wake(void* ptr, int xi) {
    elem_var_simple* p(static_cast<elem_var_simple*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

  // dom(z) inter dom(ys[i]) -> x != i.
  static void ex_x_ne_xi(void* ptr, int xi, pval_t pval, vec<clause_elt>& expl) {
    elem_var_simple* p(static_cast<elem_var_simple*>(ptr));
    
    intvar::val_t hint = p->cut_hint[xi];
    if(p->z.ub(p->s) < hint) {
      expl.push(p->z >= hint);
      expl.push(p->ys[xi] < hint);
    } else {
      expl.push(p->ys[xi] >= hint);
      expl.push(p->z < hint);
    }
  }

  static void ex_y_lb(elem_var_simple* p, int yi, intvar::val_t lb, vec<clause_elt>& expl) {
    expl.push(p->x != yi + p->base);
    expl.push(p->z < lb);
  }

  static void ex_y_ub(elem_var_simple* p, int yi, intvar::val_t ub, vec<clause_elt>& expl) {
    expl.push(p->x != yi + p->base);
    expl.push(p->z > ub);
  }

  static void ex_z_lb(P* p, int pos, intvar::val_t lb, vec<clause_elt>& expl) {
    GEAS_NOT_YET;
  }

  static void ex_z_ub(P* p, int pos, intvar::val_t lb, vec<clause_elt>& expl) {
    GEAS_NOT_YET;
  }

public:
  elem_var_simple(solver_data* _s, intvar _z, intvar _x, vec<intvar>& _ys, int _base, patom_t _r)
    : propagator(_s), base(_base), x(_x), z(_z), ys(_ys), r(_r) {
    // We assume the propagator is not half reified
    if(r != at_True) {
      GEAS_NOT_YET;
    }
     
    // Set initial explanation hints
    for(intvar& y : ys)
      cut_hint.push(y.lb(s));
  }

  void root_simplify(void) {
    
  }
    
   // FIXME
   /*
   forceinline indom(intvar& x, int k) {
     if(DOM) {
       return x.man->in_domain(x.idx, k);
     } else {
       return x.lb(s) <= k && k <= x.ub(s);
     }
   }
   */

   bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running elem_var_simple]]" << std::endl;
#endif
       
      int_itv z_dom { z.lb(s), z.ub(s) };
      int_itv z_supp { z.ub(s)+1, z.lb(s)-1 };

      // Run forward, collect supported tuples
      intvar* y = ys.begin();
      intvar* end = ys.end();
      int vv = base;

      for(; y != end; ++y, ++vv) {
        if(!in_domain(s, x, vv))
          continue;

        int_itv y_supp = z_dom & int_itv {(*y).lb(s), (*y).ub(s)};
        if(y_supp.empty()) {
          if(!enqueue(*s, x != vv, expl_thunk { ex_x_ne_xi, this, vv - base }))
            return false;
        } else {
          z_supp = y_supp;
          goto support_found;
        }
      }

      // No support, definitely false.
      // But should have failed earlier
      GEAS_ERROR;
      return false;

support_found:
      intvar* supp = y;
      for(++y, ++vv; y != end; ++y, ++vv) {
        int_itv y_supp = z_dom & int_itv {(*y).lb(s), (*y).ub(s)};
        if(y_supp.empty()) {
          if(!enqueue(*s, x != vv, expl_thunk { ex_x_ne_xi, this, vv - base }))
            return false;
        } else {
          z_supp |= y_supp;
          supp = end;
        }
      }

      if(z_supp.lb > z.lb(s)) {
        if(!set_lb(z, z_supp.lb, expl_thunk { ex_lb<ex_z_lb>, this, 0 }))
          return false;
      }

      if(z_supp.ub < z.ub(s)) {
        if(!set_ub(z, z_supp.ub, expl_thunk { ex_ub<ex_z_ub>, this, 1}))
          return false;
      }
       
      if(supp < end) {
        if(z_supp.lb > supp->lb(s)) {
          if(!set_lb(*supp, z_supp.lb, expl_thunk { ex_lb<ex_y_lb>, this, (int) (supp - ys.begin()), expl_thunk::Ex_BTPRED }))
            return false;
        }
        if(z_supp.ub < supp->ub(s)) {
          if(!set_ub(*supp, z_supp.ub, expl_thunk { ex_ub<ex_y_ub>, this, (int) (supp - ys.begin()), expl_thunk::Ex_BTPRED }))
            return false;
        }
      }
      return true;
    }

    // Constraint parameters
    int base;
    intvar x;
    intvar z;
    vec<intvar> ys;

    patom_t r;

    // Explanation hints
    vec<intvar::val_t> cut_hint;
};
#endif
int int_elem_bnd::prop_count = 0;

// enum { ELEM_DOM_MAX = 50 };
enum { ELEM_DOM_MAX = 1000 };
// enum { ELEM_DOM_MAX = 20 };
// enum { ELEM_DOM_MAX = 0 };
bool int_element(solver_data* s, intvar z, intvar x, vec<int>& ys, patom_t r) {
#if 1
  if(ys.size() < ELEM_DOM_MAX) {
//    assert(s->state.is_entailed(r));
//    new int_elem_dom(s, x, ys, z-1);
//    return true;
    // return int_element(s, r, z, x, ys, 1);
    return int_elem_bv::post(s, z, ys, x-1);
  } else {
    // new int_elem_bnd(s, r, z, x-1, ys);
    // return true;
    return int_elem_bnd::post(s, r, z, x-1, ys);
  }
#else
  return int_element(s, r, z, x, ys, 1);
#endif
}

bool elem_var_dom_dec(solver_data* s, intvar z, intvar x, vec<intvar>& ys) {
  // fprintf(stderr, "%%%% Decomposing var_int_element...\n");
  // Collect the supports for z values.
  for(int k : z.domain(s)) {
    if(!z.in_domain(s->state.p_vals, k))
      continue;

    vec<int> y_supps;
    for(int yi : irange(ys.size())) {
      if(!x.in_domain(s->state.p_vals, yi+1))
        continue;
      if(!ys[yi].in_domain(s->state.p_vals, k)) 
        continue;
      y_supps.push(yi);
    }
    if(y_supps.size() == 0) {
      if(!enqueue(*s, z != k, reason()))
        return false;
    } else if(y_supps.size() == 1) {
      int yi = y_supps[0];
      if(!add_clause(s, z != k, x == yi+1))
        return false;
      if(!add_clause(s, z != k, ys[yi] == k))
        return false;
    } else {
      vec<clause_elt> cl { z != k };
      for(int yi : y_supps) {
        patom_t at(new_bool(*s)); 
        add_clause(s, ~at, x == yi+1);
        add_clause(s, ~at, ys[yi] == k);
        add_clause(s, x != yi+1, ys[yi] != k, at);

        add_clause(s, ~at, z == k);
        cl.push(at);
      }
      if(!add_clause(*s, cl))
        return false;
    }
  }
  // Now collect supports for each index.
  for(int yi : irange(ys.size())) {
    if(!x.in_domain(s->state.p_vals, yi+1))
      continue;
    
    vec<int> y_supps;
    for(int k : z.domain(s)) {
      if(!z.in_domain(s->state.p_vals, k))
        continue;
      if(!ys[yi].in_domain(s->state.p_vals, k))
        continue; 
      y_supps.push(k);
    }
    if(y_supps.size() == 0) {
      if(!enqueue(*s, x != yi+1, reason()))
        return false;
    } else if(y_supps.size() == 1) {
      int k = y_supps[0];
      if(!add_clause(s, x != yi+1, z == k))
        return false;
      if(!add_clause(s, x != yi+1, ys[yi] == k))
        return false;
    } else {
      vec<clause_elt> cl { x != yi+1 };
      for(int k : y_supps) {
        patom_t at(new_bool(*s));
        add_clause(s, ~at, z == k);
        add_clause(s, ~at, ys[yi] == k);
        add_clause(s, at, z != k, ys[yi] != k);

        cl.push(at);
      }
      if(!add_clause(*s, cl))
        return false;
    }
  }
  return true;
}
bool var_int_element(solver_data* s, intvar z, intvar x, vec<intvar>& ys, patom_t r) {
  // new elem_var_bnd(s, z, x, ys, 1, r);
  // return true; 
#if 0
  if(z.dom_sz_exact(s->state.p_vals) <= 2 * ys.size()) {
    assert(s->state.is_entailed(r));
    return elem_var_dom_dec(s, z, x, ys);
  } else {
    return elem_var_bnd::post(s, z, x, ys, 1, r);
  }
#else
  // return elem_var_bnd::post(s, z, x, ys, 1, r);
  assert(r.lb(s->ctx()));
  #if 0
  return elem_var_dom::post(s, z, x-1, ys);
  #else
  // elem_var_env is currently only safe if the domain size is < 2^15.
  // Probably shouldn't use the domain consistent one anyway if it's more than a couple hundred.
  // Also unsafe if ys is at least 2^15. But then you've already got problems.
  if(ys.size() >= 1<<15 || z.dom_sz_approx(s->state.p_vals) > 1000)
    return elem_var_bnd::post(s, z, x, ys, 1, r);

  elem_env_man* man(elem_env_man::get(s));
  elem_var_env* env(man->find_element(s, ys));
  return env->attach_instance(x-1, z);
  #endif
#endif
}
}
