//======== Implementation of compact-table constraints ============
// Registers a manager with the solver, so we can share most of the support structures.
#include <algorithm>
#include <numeric>
#include <geas/solver/solver_data.h>
#include <geas/solver/solver_ext.h>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>

#include <geas/constraints/builtins.h>
#include <geas/constraints/mdd.h>

#include <geas/mtl/bool-set.h>
#include <geas/utils/bitset.h>

// #define TABLE_STATS
// #define WEAKEN_EXPL
#define EXPLAIN_BY_MDD

using namespace geas;

// using btset = btset::bitset;
using namespace btset;

struct table_info {
  struct val_info {
    unsigned int var;
    unsigned int val_id;
  };

  table_info(size_t _arity, size_t _num_tuples)
    : arity(_arity), num_tuples(_num_tuples)
    , domains(arity), supports(arity)
    , row_index(num_tuples)
    , m_id(-1)
    , available(1)
    , reaching(1)
    , reaching_succ(1) {
    for(int ii = 0; ii < arity; ++ii)
      forbidden.push(p_sparse_bitset(1));
  }

  size_t arity;
  size_t num_tuples;

  // Incoming/outgoing edges for each state
  // support_set* val_support;
  support_set& val_supports(size_t x, size_t k) { return supports[x][k]; }

  // Reconstruct the tuples, but in terms of value indices (not
  // actual values).
  // void rebuild_index_tuples(vec< vec<int> >& out_tuples);
  void rebuild_proj_tuples(int var, int val_id, vec<vec<int> >& out_tuples);

  // Initial domains (and mappings from value-id to actual value)
  vec< vec<int> > domains;
  vec< vec<support_set> > supports;

  vec<int> vals_start;
  vec<val_info> val_index;
  vec< vec<int> > row_index;

  // In the mdd, values are indices into domains, not
  // the values themselves.
  mdd::mdd_id m_id;
  vec<mdd::mdd_id> val_mdds;

  // Scratch space.
  p_sparse_bitset available;
  p_sparse_bitset reaching;
  p_sparse_bitset reaching_succ;
  vec<p_sparse_bitset> forbidden;
};

table_info* construct_table_info(vec< vec<int> >& tuples) {
  assert(tuples.size() > 0);
  unsigned int sz(tuples.size());
  unsigned int arity(tuples[0].size());

  vec<int> tperm(tuples.size());
  for(int ii = 0; ii < tuples.size(); ii++)
    tperm[ii] = ii;
  
  table_info* ti(new table_info(arity, sz));

  // Compute the set of values & supports for each variable.
  for(unsigned int xi = 0; xi < arity; ++xi) {
    // Sort tuples by xi-value.
    ti->vals_start.push(ti->val_index.size());

    std::sort(tperm.begin(), tperm.end(),
      [&tuples, xi](int ii, int jj) {
        if(tuples[ii][xi] == tuples[jj][xi]) return ii < jj;
        return tuples[ii][xi] < tuples[jj][xi];
      });
    
    // Now we can iterate through, and collect (a) values, and (b) support tuples.
    int v(tuples[tperm[0]][xi]);
    vec<int> v_rows { tperm[0] };
    ti->row_index[tperm[0]].push(ti->val_index.size());
    unsigned int k = 0;

    for(int ii = 1; ii < tperm.size(); ++ii) {
      int t(tperm[ii]);

      if(tuples[t][xi] != v) {
        // Finished supports for v.
        ti->val_index.push(table_info::val_info { xi, k });
        ti->domains[xi].push(v);
        ti->supports[xi].push(support_set(v_rows.begin(), v_rows.end()));
        ti->val_mdds.push(-1);
        ++k;
        v = tuples[t][xi];
        v_rows.clear();
      }
      v_rows.push(t);
      ti->row_index[t].push(ti->val_index.size());
    }
    ti->val_index.push(table_info::val_info { xi, k });
    ti->domains[xi].push(v);
    ti->supports[xi].push(support_set(v_rows.begin(), v_rows.end()));
    ti->val_mdds.push(-1);
  }
  return ti;
}

/*
void table_info::rebuild_index_tuples(vec< vec<int> >& out_tuples) {
  out_tuples.clear();
  for(const vec<int>& r : row_index) {
    out_tuples.push();
    for(int v : r) {
      out_tuples.last().push(val_index[v].val_id);
    }
  }
}
*/

void table_info::rebuild_proj_tuples(int var, int val_id, vec< vec<int> >& out_tuples) {
  out_tuples.clear();
  for(auto e : supports[var][val_id]) {
    int base(word_bits() * e.w);
    word_ty bits(e.bits);
    while(bits) {
      int ri = base + __builtin_ctzll(bits);
      vec<int>& r(row_index[ri]);
      bits &= bits-1;
      assert(r[var] == vals_start[var] + val_id);

      out_tuples.push();
      for(int vi = 0; vi < var; ++vi)
        // out_tuples.last().push(val_index[r[vi]].val_id);
        out_tuples.last().push(r[vi]);
      for(int vi = var+1; vi < r.size(); ++vi)
        // out_tuples.last().push(val_index[r[vi]].val_id);
        out_tuples.last().push(r[vi]);
    }
  }
}

class table_manager : public solver_ext<table_manager> {
public:
  table_manager(solver_data* s) { }
  ~table_manager(void) {
    for(table_info* ti : tables)
      delete ti;     
  }
   
  // Don't bother doing CSE on tables, rely on the caller knowing
  // when tables are re-used.
  table_id build(vec< vec<int> >& tuples);
  table_info& lookup(table_id r) { return *(tables[r]); }
protected:
  vec<table_info*> tables;
};

table_id table_manager::build(vec< vec<int> >& tuples) {
  table_id id(tables.size());
  tables.push(construct_table_info(tuples));
  return id;
}

class compact_table : public propagator, public prop_inst<compact_table> {
  watch_result wakeup(int vi) {
    auto info(table.val_index[vi]);
    if(live_vals[info.var].elem(info.val_id)) {
      if(!changed_vars.elem(info.var)) {
        queue_prop();
        changed_vars.add(info.var);
        old_live[info.var] = live_vals[info.var].size();
        trail_push(s->persist, live_vals[info.var].sz);
      }
      live_vals[info.var].remove(info.val_id);

      trail_push(s->persist, dead_vals.sz);
      dead_pos[vi] = dead_vals.size();
      dead_vals.insert(vi);
    }
    return Wt_Keep;
  }

  inline bool var_fixed_at(int xi, unsigned int dead_idx) {
    if(live_vals[xi].size() > 1)
      return false;
    // Look at the second value
    return dead_pos[table.vals_start[xi] + live_vals[xi][1]] < (int) dead_idx;
  }

  void mdd_mark_forbidden(mdd::mdd_info& m, unsigned int dead_idx) {
    /*
    p_sparse_bitset& reaching(table.reaching);
    p_sparse_bitset& reaching_succ(table.reaching_succ);
    p_sparse_bitset& available(table.available);
    vec<p_sparse_bitset>& forbidden(table.forbidden);
    */

    table.reaching.clear();
    table.reaching.fill(m.num_edges.last());
    for(int l = m.values.size()-1; l > 0; --l) {
      table.available.clear();
      for(int k : irange(m.values[l].size())) {
        if(dead_vals.pos(m.values[l][k]) < dead_idx)
          continue;
        table.available.union_with(m.val_support[l][k]);
      }

      table.forbidden[l].set(table.reaching);
      table.forbidden[l].remove(table.available);
      table.reaching.intersect_with(table.available);

      table.reaching_succ.clear();
      for(int ni = 0; ni < m.num_nodes[l]; ++ni) {
        if(table.reaching.has_intersection(m.edge_HD[l][ni]))
          table.reaching_succ.union_with(m.edge_TL[l][ni]);
      }
      // table.reaching.set(table.reaching_succ);
      std::swap(table.reaching, table.reaching_succ);
    }
    table.forbidden[0].set(table.reaching);
  }
  void mdd_retrieve_expln(mdd::mdd_info& m, unsigned int dead_idx, vec<clause_elt>& expl) {
    /*
    p_sparse_bitset& reaching(table.reaching);
    p_sparse_bitset& reaching_succ(table.reaching_succ);
    vec<p_sparse_bitset>& forbidden(table.forbidden);
    */

    table.reaching.fill(m.num_edges[0]);
    for(int l = 0; l < m.values.size(); ++l) {
      for(int w : table.forbidden[l].idx) {
        if(!table.reaching.idx.elem(w))
          continue;
        word_ty f_bits(table.forbidden[l][w]);
        // If there is some edge which must be blocked here, add
        // the corresponding value to the explanation, and remove
        // all matching edges.
        while(table.reaching[w] & f_bits) {
          int f_edge = word_bits() * w + __builtin_ctzll(table.reaching[w] & f_bits);
          int v_id = m.edge_value_id[l][f_edge];
          table.reaching.remove(m.val_support[l][v_id]);
          int xi(table.val_index[m.values[l][v_id]].var);
          int k(table.domains[xi][table.val_index[m.values[l][v_id]].val_id]);
          xs[xi].explain_neq(k, expl);
        }
      }
      if(table.reaching.is_empty())
        return;
      
      assert(l+1 < m.values.size());
      table.reaching_succ.clear();
      for(int ni = 0; ni < m.num_nodes[l+1]; ++ni) {
        if(table.reaching.has_intersection(m.edge_TL[l+1][ni])) {
          table.reaching_succ.union_with(m.edge_HD[l+1][ni]);
        }
      }
      // table.reaching.set(table.reaching_succ);
      std::swap(table.reaching, table.reaching_succ);
    }
  }

  void expl_from_mdd(mdd::mdd_info& m, unsigned int dead_idx, vec<clause_elt>& expl) {
    mdd_mark_forbidden(m, dead_idx);
    mdd_retrieve_expln(m, dead_idx, expl);
  }
  /*
  void expl_from_mdd(vec<int>& proj_vars, mdd::mdd_info& m, unsigned int dead_idx, vec<clause_elt>& expl) {
    // Mark the set of edges which, currently, have a path to true.
    // Available stores the values consistent 
    reaching[table.arity].fill(m.num_edges[table.arity-1]);
    for(int xi = table.arity-1; xi > 0; --xi) {
      // Collect the interesting values
      available.clear();
      for(int k : live_vals[xi].all_values()) {
        if(dead_idx <= dead_pos[table.vals_start[xi] + k])
          continue;
        available.union_with(m.val_support[xi][k]);
      }
      
      reaching[xi].clear();
      for(int n : irange(m.num_nodes[l])) {
        if(reaching[xi+1].has_intersection(m.edge_hd[xi][n])) {
          reaching[xi].union_with(m.edge_tl[xi][n]);
        }
      }
      reaching[xi].intersect_with(available);
    }
    

    // Walk back down the MDD, collecting the actual explanation.
    reached.clear();
    int x0(0);
    for(int k : irange(m.val_support[0].size())) {
      if(dead_pos[table.vals_start[x0] + k] < dead_idx) {
        // Could appear in the explanation 
        if(reaching[0].has_intersection(m.val_support[0][k])) {
          // Must be in the explanation
          xs[x0].explain_neq(table.domains[x0][k], expl);
          continue;
        }
      }
      reached.union_with(m.val_support[0][k]);
    }

    for(int l = 1; l < proj_vars.size(); ++l) {
      // Collect the set of edges we _could_ traverse, if
      // domains were unconstrained.
      int xi(proj_vars[l]);
      reached[l].clear();
      for(int n : irange(m.num_nodes[l])) { 
        if(reached[l-1].has_intersection(m.edge_TL[l][n]))
          reached[l].union_with(m.edge_HD[l][n]);
      }
      
      for(int k : irange(m.val_support[l].size())) {
        if(dead_pos[table.vals_start[xi] + k] < dead_idx) {
          for(auto e : m.val_support[l][k]) {
            if(reached.idx.elem(e.w) && reaching[l].idx.elem(e.w)) {
              if(e.bits & reached[e.w] & reaching[l][e.w]) {
                // Value must be forbidden     
                xs[xi].explain_neq(table.domains[xi][k], expl);
                reached[l].remove(m.val_support[l][k]);
                goto next_value;
              }
            }
          }
        }
    next_value:
      continue;
      }
      if(reached[l].empty())
        return;
    }
  }
  */

  // Assumes ex_tuples has been initialized appropriately.
  void mk_expl(unsigned int dead_idx, vec<clause_elt>& expl) {
    // Walk through the available values
#if 1
    // fprintf(stderr, "%% %d words of %d\n", ex_tuples.idx.size(), live_tuples.num_words());
    auto b(ex_tuples.idx.begin());
    auto e(ex_tuples.idx.end());
#ifdef WEAKEN_EXPL
restart_expl:
#endif
    for(; b != e; ++b) {
      int w(*b);
      while(ex_tuples[w]) {
        // Which row 
        size_t r(w * word_bits() + __builtin_ctzll(ex_tuples[w]));
        for(int vi : table.row_index[r]) {
          if(dead_vals.pos(vi) < dead_idx) {
            // Value is available for expln.
            table_info::val_info info(table.val_index[vi]);
#ifdef WEAKEN_EXPL
            if(var_fixed_at(info.var, dead_idx)) {
              // Variable is fixed, use this instead.
              int ex_v(live_vals[info.var][0]);
              xs[info.var].explain_eq(table.domains[info.var][ex_v], expl);
              unsigned int old_sz = ex_tuples.idx.size();
              ex_tuples.idx.clear();
              for(auto e : table.supports[info.var][ex_v]) {
                if(ex_tuples.idx.pos(e.w) < old_sz) {
                  if(ex_tuples[e.w] & e.bits) {
                    ex_tuples[e.w] &= e.bits;
                    ex_tuples.idx.insert(e.w);
                  }
                }
              }
              b = ex_tuples.idx.begin();
              e = ex_tuples.idx.end();
              goto restart_expl;
            }
#endif
            xs[info.var].explain_neq(table.domains[info.var][info.val_id], expl);
            for(auto e : table.supports[info.var][info.val_id]) {
              ex_tuples[e.w] &= ~e.bits;
            }
            goto next_row;
          }
        }
        GEAS_ERROR;
     next_row:
        continue;
      }
    }
#else
    for(unsigned int vi : dead_vals.slice(0, dead_idx)) {
      table_info::val_info info(table.val_index[vi]);
      xs[info.var].explain_neq(table.domains[info.var][info.val_id], expl);
      ex_tuples.clear();
    }
    assert(ex_tuples.is_empty());
#endif
  }

  void print_stats(void) {
#ifdef TABLE_STATS
    int used_count(0);
    for(size_t ii = 0; ii < used_rows.num_words(); ++ii)
      used_count += __builtin_popcountll(used_rows[ii]);
    fprintf(stderr, "%% prop(%d): used %d of %d. %d wipeouts\n", prop_id, used_count, (int) table.num_tuples, wipeouts);
#endif
  }

#ifdef TABLE_STATS
  int median_of(vec<int>& xs) {
    vec<int> perm;
    for(int ii : irange(xs.size()))
      perm.push(ii);
    std::nth_element(perm.begin(), perm.begin() + (perm.end() - perm.begin())/2, perm.end(),
      [&xs](int i, int j) { return xs[i] < xs[j]; }); 
    return xs[perm[perm.size()/2]];
  }

  void report_internal(void) {
    int total_uses = std::accumulate(ex_count.begin(), ex_count.end(), 0);
    int max_uses = *std::max_element(ex_count.begin(), ex_count.end());
    int median_uses = median_of(ex_count);
    int total_props = std::accumulate(prop_count.begin(), prop_count.end(), 0);
    int max_props = *std::max_element(prop_count.begin(), prop_count.end());
    fprintf(stderr, "%% compact-table[%d|%d]: arity %d, size %d, vals %d\n", cons_id, prop_id, (int) table.arity, (int) table.num_tuples, table.val_index.size());
    fprintf(stderr, "%%%%  %d wipeouts, explanations: %.02lf mean, %d median, %d max\n", wipeouts, 1.0*total_uses/ex_count.size(), median_uses, max_uses);
    fprintf(stderr, "%%%%  propagations: %.02lf mean, %d max", 1.0*total_props/prop_count.size(), max_props);
    fprintf(stderr, "\n");
  }
#endif

  void ex_val(int vi, pval_t _pi, vec<clause_elt>& expl) {
    int dead_idx(dead_pos[vi]);
    // Construct the MDD
    if(table.val_mdds[vi] < 0) {
      vec< vec<int> > tuples;
      table.rebuild_proj_tuples(table.val_index[vi].var, table.val_index[vi].val_id, tuples);
      table.val_mdds[vi] = mdd::of_tuples(s, tuples);
      mdd::mdd_info& mi(mdd::lookup(s, table.val_mdds[vi]));
      /*
      int num_nodes = std::accumulate(mi.num_nodes.begin(), mi.num_nodes.end(), 0);
      int num_edges = std::accumulate(mi.num_edges.begin(), mi.num_edges.end(), 0);
      fprintf(stderr, "MDD id: %d (%d nodes, %d edges) {P %p}\n", table.val_mdds[vi], num_nodes, num_edges, &table);
      */

      int width_max = std::accumulate(mi.num_edges.begin(), mi.num_edges.end(), 0, [](unsigned int i, unsigned int j) { return std::max(i, j); });
      table.available.growTo(width_max);
      table.reaching.growTo(width_max);
      table.reaching_succ.growTo(width_max);
      for(p_sparse_bitset& f : table.forbidden)
        f.growTo(width_max);

    }

#ifdef EXPLAIN_BY_MDD
#ifdef TABLE_STATS
    ex_count[vi]++;
#endif
    expl_from_mdd(mdd::lookup(s, table.val_mdds[vi]), dead_idx, expl);
#else
    // Collect the set of tuples we need to explain.
    table_info::val_info ex_info(table.val_index[vi]);
#ifdef TABLE_STATS
    ex_count[vi]++;
    for(auto s : table.supports[ex_info.var][ex_info.val_id])
      used_rows[s.w] |= s.bits;
    // print_stats();
#endif
      
    ex_tuples.init(table.supports[ex_info.var][ex_info.val_id]);
    mk_expl(dead_idx, expl);
#ifdef TABLE_STATS
    // fprintf(stderr, "%% ex-size: %d\n", expl.size());
#endif
#endif
  }

  void ex_fail(vec<clause_elt>& expl) {
#ifdef TABLE_STATS
    ++wipeouts;
#endif
    // Construct the MDD
    if(table.m_id < 0) {
      vec< vec<int> > tuples;
      // table.rebuild_index_tuples(tuples);
      table.m_id = mdd::of_tuples(s, table.row_index);
      mdd::mdd_info& mi(mdd::lookup(s, table.m_id));
      /*
      int num_nodes = std::accumulate(mi.num_nodes.begin(), mi.num_nodes.end(), 0);
      int num_edges = std::accumulate(mi.num_edges.begin(), mi.num_edges.end(), 0);
      fprintf(stderr, "MDD id: %d (%d nodes, %d edges) {T %p}\n", table.m_id, num_nodes, num_edges, &table);
      */

      // Grow the scratch-space.
      int width_max = std::accumulate(mi.num_edges.begin(), mi.num_edges.end(), 0, [](unsigned int i, unsigned int j) { return std::max(i, j); });
      table.available.growTo(width_max);
      table.reaching.growTo(width_max);
      table.reaching_succ.growTo(width_max);
      for(p_sparse_bitset& f : table.forbidden)
        f.growTo(width_max);
    }
#ifdef EXPLAIN_BY_MDD
    expl_from_mdd(mdd::lookup(s, table.m_id), dead_vals.size(), expl);
#else
    ex_tuples.fill(table.num_tuples);
    mk_expl(dead_vals.size(), expl);
#endif
  }

public:
  compact_table(solver_data* s, table_id t, vec<intvar>& _xs)
    : propagator(s), table(table_manager::get(s)->lookup(t)), xs(_xs)
    , live_vals(xs.size())
    , live_tuples(table.num_tuples)
    , live_r(0)
    , residual(table.val_index.size(), 0)
    , active_vars(xs.size())
    , dead_vals(table.val_index.size())
    , dead_pos(table.val_index.size(), 0)
    , changed_vars(xs.size())
    , old_live(xs.size(), 0)
    , ex_tuples(table.num_tuples)
#ifdef TABLE_STATS
    , used_rows(table.num_tuples)
    , wipeouts(0)
    , ex_count(table.val_index.size(), 0)
    , prop_count(table.val_index.size(), 0)
#endif
    {

    memset(ex_tuples.mem, 0, sizeof(word_ty) * ex_tuples.cap);
    live_tuples.fill(table.num_tuples);

    for(int xi : irange(xs.size())) {
      vec<int>& d(table.domains[xi]);
      make_sparse(xs[xi], d);
      live_vals[xi].growTo(d.size());
      for(int k : irange(d.size())) {
        patom_t at(xs[xi] != d[k]);
        val_atoms.push(at);
        if(in_domain(xs[xi], d[k])) {
          // attach(s, xs[xi] != d[k], watch<&P::wakeup>(table.vals_start[xi] + k));
          attach(s, at, watch<&P::wakeup>(table.vals_start[xi] + k));
          live_vals[xi].insert(k);
        } else {
          dead_pos[table.vals_start[xi] + k] = dead_vals.size();
          dead_vals.insert(table.vals_start[xi] + k);
        }
      }
      if(live_vals.size() > 1)
        active_vars.insert(xi);

      if(live_vals[xi].size() != (unsigned int) d.size()) {
        changed_vars.add(xi);
        old_live[xi] = d.size();
      }
    }
    queue_prop();
  }

  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
  bool check_sat(ctx_t& ctx) {
    for(const vec<int>& r : table.row_index) {
      for(int vi : r) {
        table_info::val_info info(table.val_index[vi]);
        if(!xs[info.var].in_domain_exhaustive(ctx, table.domains[info.var][info.val_id]))
          goto next_row;
      }
      return true;
    next_row:
      continue;
    }
    return false;
  }

  bool filter(vec<clause_elt>& confl) {
    // Iterate in reverse, so we can safely remove values.
    unsigned int act_sz = active_vars.size();
    for(unsigned int x : active_vars.rev()) {
      unsigned int x_sz = live_vals[x].size();
      for(unsigned int k : live_vals[x].rev()) {
        // Check if there is still some support for x = k.
        support_set& ss(table.supports[x][k]);
        int val_idx = table.vals_start[x] + k;
        auto r(ss[residual[val_idx]]);

        if(live_tuples[r.w] & r.bits)
          goto next_value;

        // Otherwise, search for a new support.
        {
        auto b(ss.begin());
        auto e(ss.end());

          for(; b != e; ++b) {
            if(live_tuples[(*b).w] & (*b).bits) {
              // Found a new support
              residual[val_idx] = (b - ss.begin());   
              goto next_value;
            }
          }
        }
        // No supports left. Try removing it from the domain of x.
        // dead_vals.insert(table.vals_start[x] + k);
        dead_pos[val_idx] = dead_vals.size();
#ifdef TABLE_STATS
        prop_count[val_idx]++;
#endif
        if(!enqueue(*s, val_atoms[val_idx] /*xs[x] != table.domains[x][k]*/, expl<&P::ex_val>(val_idx))) {
          // dead_vals.sz--;
          active_vars.sz = act_sz;
          live_vals[x].sz = x_sz;
          return false;
        }
        // trail_fake(s->persist, dead_vals.sz, dead_vals.sz-1);
        live_vals[x].remove(k);
    next_value:
        continue;
      }
      // If some value was killed, make sure it'll get restored on backtracking.
      if(live_vals[x].size() != x_sz) {
        trail_fake(s->persist, live_vals[x].sz, x_sz);
        // If x is now fixed, we never need to check it again.
        if(live_vals[x].size() == 1) {
          trail_push(s->persist, active_vars.sz);
          active_vars.remove(x);
        }
      }
    }
    // If some variable was disabled, save the old value
    if(active_vars.size() != act_sz)
      trail_fake(s->persist, active_vars.sz, act_sz);
    return true;
  }

  void update_tuples(void) {
    for(unsigned int x : changed_vars) {
      p_sparseset& x_vals(live_vals[x]);
      // Ignore resetting for now.

      for(unsigned int k : x_vals.slice(x_vals.size(), old_live[x])) {
        kill_value(x, k);
      }
    }
    changed_vars.clear();
  }

  bool tuples_nonempty(void) {
    if(live_tuples[live_r])
      return true;
    for(int w : irange(live_tuples.size())) {
      if(live_tuples[w]) {
        live_r = w;
        return true;
      }
    }
    return false;
  }

  bool propagate(vec<clause_elt>& confl) {
    update_tuples();
    if(!tuples_nonempty()) {
      ex_fail(confl);
      return false;
    }
    if(!filter(confl))
      return false;

    return true;
  }
   
  void cleanup(void) {
    is_queued = false;
    changed_vars.clear();
  }

protected:
  // Compute S - T, returning true if S changed (so S & T was non-empty).
  bool try_remove_bits(p_sparse_bitset& bits, support_set& rem) {
    auto it(rem.begin());
    auto en(rem.end());
    // Search for a word with non-empty intersection with bits.
    for(; it != en; ++it) {
      unsigned int w((*it).w);
      if(!bits.idx.elem(w))
        continue;
      if(bits[w] & (*it).bits) {
        // Non-empty. Remove bits in this word...
        word_ty r(bits[w] & ~(*it).bits);
        bits[w] = r;
        if(!r) bits.idx.remove(w);

        // And any remaining words.
        for(++it; it != en; ++it) {
          unsigned int w((*it).w);
          if(!bits.idx.elem(w))
            continue;
          word_ty r(bits[w] & ~(*it).bits);
          bits[w] = r;
          if(!r) bits.idx.remove(w);
        }
        return true;
      }
    }
    return false;
  }

  inline void word_remove(bitset& bits, support_set::elem_ty e) {
    if(bits[e.w] & e.bits) {
      trail_change(s->persist, bits[e.w], bits[e.w] & ~e.bits);
    }
  }

  void kill_value(unsigned int x, unsigned int k) {
    support_set& ss(table.supports[x][k]);
    for(support_set::elem_ty e : ss) {
      word_remove(live_tuples, e);
    }
  }

  // The pre-computed table information
  table_info& table;

  // Parameters
  vec<intvar> xs;
  vec<patom_t> val_atoms;

  // Persistent state
  vec<p_sparseset> live_vals;
  bitset live_tuples;
  unsigned int live_r;

  vec<unsigned int> residual;
  p_sparseset active_vars;

  // We use dead_vals to reconstruct
  // the state upon explanation.
  // Only records the _externally_ killed values.
  p_sparseset dead_vals;
  vec<int> dead_pos;

  // Transient data
  boolset changed_vars;
  vec<unsigned int> old_live;

  p_sparse_bitset ex_tuples;
  
#ifdef TABLE_STATS
  bitset used_rows;
  unsigned int wipeouts;
  vec<int> ex_count;
  vec<int> prop_count;
#endif
};

// Introduces Boolean row variables
class compact_table_rvar : public propagator, public prop_inst<compact_table_rvar> {
  watch_result wakeup(int vi) {
    auto info(table.val_index[vi]);
    if(live_vals[info.var].elem(info.val_id)) {
      if(!changed_vars.elem(info.var)) {
        queue_prop();
        changed_vars.add(info.var);
        old_live[info.var] = live_vals[info.var].size();
        trail_push(s->persist, live_vals[info.var].sz);
      }
      live_vals[info.var].remove(info.val_id);
    }
    return Wt_Keep;
  }

  watch_result wake_row(int ri) {
    unsigned int w(elt_idx(ri));  
    word_ty b(elt_mask(ri));
    if(live_tuples[w] & b) {
      trail_push(s->persist, live_tuples[w]);
      live_tuples[w] &= ~b;
      queue_prop();
    }
    return Wt_Keep;
  } 
  void print_stats(void) {
#ifdef TABLE_STATS
    int used_count(0);
    for(int ii = 0; ii < used_rows.num_words(); ++ii)
      used_count += __builtin_popcountll(used_rows[ii]);
    fprintf(stderr, "%% prop(%d): used %d of %d. %d wipeouts\n", prop_id, used_count, (int) table.num_tuples, wipeouts);
#endif
  }

  void ex_val(int vi, pval_t _pi, vec<clause_elt>& expl) {
    // Collect the set of tuples we need to explain.
    table_info::val_info ex_info(table.val_index[vi]);

    for(auto e : table.supports[ex_info.var][ex_info.val_id]) {
      unsigned int base(e.w * word_bits());
      word_ty bits(e.bits);
      while(bits) {
        expl.push(row_vars[base + __builtin_ctzll(bits)]);
        bits &= (bits-1); // Clear lowest bit.
      }
    }
  }

  void ex_fail(vec<clause_elt>& expl) {
#ifdef TABLE_STATS
    ++wipeouts;
#endif
    for(patom_t r : row_vars)
      expl.push(r);
  }

public:
  compact_table_rvar(solver_data* s, table_id t, vec<intvar>& _xs)
    : propagator(s), table(table_manager::get(s)->lookup(t)), xs(_xs)
    , live_vals(xs.size())
    , live_tuples(table.num_tuples)
    , live_r(0)
    , residual(table.val_index.size(), 0)
    , active_vars(xs.size())
    , changed_vars(xs.size())
    , old_live(xs.size(), 0)
    , ex_tuples(table.num_tuples)
#ifdef TABLE_STATS
    , used_rows(table.num_tuples)
    , wipeouts(0)
#endif
    {

    memset(ex_tuples.mem, 0, sizeof(word_ty) * ex_tuples.cap);
    live_tuples.fill(table.num_tuples);

    for(int ri = 0; ri < table.num_tuples; ++ri) {
      patom_t r(new_bool(*s));
      attach(s, ~r, watch<&P::wake_row>(row_vars.size()));
      row_vars.push(r);
    }

    for(int xi : irange(xs.size())) {
      vec<int>& d(table.domains[xi]);
      make_sparse(xs[xi], d);
      live_vals[xi].growTo(d.size());
      for(int k : irange(d.size())) {
        if(in_domain(xs[xi], d[k])) {
          attach(s, xs[xi] != d[k], watch<&P::wakeup>(table.vals_start[xi] + k));
          live_vals[xi].insert(k);
        }
      }
      if(live_vals.size() > 1)
        active_vars.insert(xi);

      if(live_vals[xi].size() != (unsigned int) d.size()) {
        changed_vars.add(xi);
        old_live[xi] = d.size();
      }
    }
    queue_prop();
  }

  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
  bool check_sat(ctx_t& ctx) {
    for(const vec<int>& r : table.row_index) {
      for(int vi : r) {
        table_info::val_info info(table.val_index[vi]);
        if(!xs[info.var].in_domain_exhaustive(ctx, table.domains[info.var][info.val_id]))
          goto next_row;
      }
      return true;
    next_row:
      continue;
    }
    return false;
  }

  bool filter(vec<clause_elt>& confl) {
    // Iterate in reverse, so we can safely remove values.
    unsigned int act_sz = active_vars.size();
    for(unsigned int x : active_vars.rev()) {
      unsigned int x_sz = live_vals[x].size();
      for(unsigned int k : live_vals[x].rev()) {
        // Check if there is still some support for x = k.
        support_set& ss(table.supports[x][k]);
        int val_idx = table.vals_start[x] + k;
        auto r(ss[residual[val_idx]]);

        if(live_tuples[r.w] & r.bits)
          goto next_value;

        // Otherwise, search for a new support.
        {
        auto b(ss.begin());
        auto e(ss.end());

          for(; b != e; ++b) {
            if(live_tuples[(*b).w] & (*b).bits) {
              // Found a new support
              residual[val_idx] = (b - ss.begin());   
              goto next_value;
            }
          }
        }
        // No supports left. Try removing it from the domain of x.
        // dead_vals.insert(table.vals_start[x] + k);
        if(!enqueue(*s, xs[x] != table.domains[x][k], expl<&P::ex_val>(val_idx))) {
          active_vars.sz = act_sz;
          live_vals[x].sz = x_sz;
          return false;
        }
        live_vals[x].remove(k);
    next_value:
        continue;
      }
      // If some value was killed, make sure it'll get restored on backtracking.
      if(live_vals[x].size() != x_sz) {
        trail_fake(s->persist, live_vals[x].sz, x_sz);
        // If x is now fixed, we never need to check it again.
        if(live_vals[x].size() == 1) {
          trail_push(s->persist, active_vars.sz);
          active_vars.remove(x);
        }
      }
    }
    // If some variable was disabled, save the old value
    if(active_vars.size() != act_sz)
      trail_fake(s->persist, active_vars.sz, act_sz);
    return true;
  }

  bool update_tuples(void) {
    for(unsigned int x : changed_vars) {
      p_sparseset& x_vals(live_vals[x]);
      // Ignore resetting for now.

      for(unsigned int k : x_vals.slice(x_vals.size(), old_live[x])) {
        if(!kill_value(x, k))
          return false;
      }
    }
    changed_vars.clear();
    return true;
  }

  bool tuples_nonempty(void) {
    if(live_tuples[live_r])
      return true;
    for(int w : irange(live_tuples.size())) {
      if(live_tuples[w]) {
        live_r = w;
        return true;
      }
    }
    return false;
  }

  bool propagate(vec<clause_elt>& confl) {
    if(!update_tuples())
      return false;
    if(!tuples_nonempty()) {
      ex_fail(confl);
      return false;
    }
    if(!filter(confl))
      return false;

    return true;
  }
   
  void cleanup(void) {
    is_queued = false;
    changed_vars.clear();
  }

protected:
  // Compute S - T, returning true if S changed (so S & T was non-empty).
  bool try_remove_bits(p_sparse_bitset& bits, support_set& rem) {
    auto it(rem.begin());
    auto en(rem.end());
    // Search for a word with non-empty intersection with bits.
    for(; it != en; ++it) {
      unsigned int w((*it).w);
      if(!bits.idx.elem(w))
        continue;
      if(bits[w] & (*it).bits) {
        // Non-empty. Remove bits in this word...
        word_ty r(bits[w] & ~(*it).bits);
        bits[w] = r;
        if(!r) bits.idx.remove(w);

        // And any remaining words.
        for(++it; it != en; ++it) {
          unsigned int w((*it).w);
          if(!bits.idx.elem(w))
            continue;
          word_ty r(bits[w] & ~(*it).bits);
          bits[w] = r;
          if(!r) bits.idx.remove(w);
        }
        return true;
      }
    }
    return false;
  }

  inline bool word_remove(bitset& bits, support_set::elem_ty e, patom_t at) {
    if(bits[e.w] & e.bits) {
      unsigned int base(e.w * word_bits());
      word_ty rem(bits[e.w] & e.bits);
      while(rem) {
        if(!enqueue(*s, ~row_vars[base + __builtin_ctzll(rem)], at))
          return false;
        rem &= rem-1;
      }
      trail_change(s->persist, bits[e.w], bits[e.w] & ~e.bits);
    }
    return true;
  }

  bool kill_value(unsigned int x, unsigned int k) {
    support_set& ss(table.supports[x][k]);
    patom_t at(xs[x] == table.domains[x][k]);
    for(support_set::elem_ty e : ss) {
      if(!word_remove(live_tuples, e, at))
        return false;
    }
    return true;
  }

  // The pre-computed table information
  table_info& table;

  // Parameters
  vec<intvar> xs;
  vec<patom_t> row_vars;

  // Persistent state
  vec<p_sparseset> live_vals;
  bitset live_tuples;
  unsigned int live_r;

  vec<unsigned int> residual;
  p_sparseset active_vars;

  // We use dead_vals to reconstruct
  // the state upon explanation.
  // Only records the _externally_ killed values.
  p_sparseset dead_vals;
  vec<int> dead_pos;

  // Transient data
  boolset changed_vars;
  vec<unsigned int> old_live;

  p_sparse_bitset ex_tuples;

#ifdef TABLE_STATS
  bitset used_rows;
  unsigned int wipeouts;
#endif
};

namespace geas {

namespace table {
  table_id build(solver_data* s, vec< vec<int> >& rows) {
    return table_manager::get(s)->build(rows);    
  }

  bool decompose(solver_data* s, table_info& t, vec<intvar>& xs) {
    intvar rvar(new_intvar(s, 0, t.num_tuples-1));
    
    vec< vec<patom_t> > dom_atoms(xs.size());
    for(int xi : irange(xs.size())) {
      for(int k : t.domains[xi])
        dom_atoms[xi].push(xs[xi] == k);
    }

    // Clauses for each row
    for(int ri : irange(t.row_index.size())) {
      patom_t at(rvar != ri);
      for(int v : t.row_index[ri]) {
        table_info::val_info info(t.val_index[v]);
        if(!add_clause(s, at, dom_atoms[info.var][info.val_id]))
          return false;
      }
    }
    // Clauses for each value
    for(table_info::val_info info : t.val_index) {
      vec<clause_elt> cl { ~dom_atoms[info.var][info.val_id] };
      for(auto e : t.supports[info.var][info.val_id]) {
        int base(word_bits() * e.w);
        word_ty bits(e.bits);
        while(bits) {
          int r(base + __builtin_ctzll(bits));
          bits &= bits-1;
          cl.push(rvar == r); 
        }
      }
      if(!add_clause(*s, cl))
        return false;
    }
    return true;
  }
  bool decompose_elem(solver_data* s, table_info& t, vec<intvar>& xs) {
    intvar r(new_intvar(s, 1, t.num_tuples));
    for(int xi : irange(xs.size())) {
      vec<int> ys;
      for(vec<int>& r : t.row_index) {
        assert(r.size() == xs.size());
        int vi(r[xi]);
        assert(t.val_index[vi].var == xi);
        ys.push(t.domains[xi][t.val_index[vi].val_id]);
      }
      if(!int_element(s, xs[xi], r, ys, at_True))
        return false;
    }
    return true;
  }

  bool post(solver_data* s, table_id t, vec<intvar>& xs, TableMode m) {
    switch(m) {
      case Table_Clause:
        return decompose(s, table_manager::get(s)->lookup(t), xs);
      case Table_Elem:
        return decompose_elem(s, table_manager::get(s)->lookup(t), xs);
      case Table_CT:
      case Table_Default:
        return compact_table::post(s, t, xs);
    //   return compact_table_rvar::post(s, t, xs);
    }
    GEAS_ERROR;
    return false;
  }
}

}
