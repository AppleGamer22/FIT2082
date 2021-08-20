#include <algorithm>
#include <geas/solver/solver_data.h>
#include <geas/solver/solver_debug.h>
#include <geas/engine/conflict.h>

#include <geas/mtl/bool-set.h>

// #define CHECK_PRED_EVALS
// #define CHECK_CLEVEL
namespace geas {

// ex_val is the bound which must be entailed
static inline void bump_clause_act(solver_data* s, clause& cl) {
  cl.extra.act += s->learnt_act_inc;
}
static inline void decay_clause_act(solver_data* s) {
  if((s->learnt_act_inc *= s->opts.learnt_act_growthrate) > 1e20) {
    for(clause* c : s->infer.learnts) {
      c->extra.act *= 1e-20;
    }
    s->learnt_act_inc *= 1e-20;
  }
}

#if 0
static inline void bump_pred_act(solver_data* s, pid_t p) {
  // FIXME: Update order in heap, also.
  /*
  s->infer.pred_act[p] += s->pred_act_inc;
  if(s->pred_heap.inHeap(p))
    s->pred_heap.decrease(p);
  */
  /*
  unsigned int x = p>>1;
  s->infer.pred_act[x] += s->pred_act_inc;
  if(s->pred_heap.inHeap(x))
    s->pred_heap.decrease(x);
  */
}
#endif

struct cmp_clause_act {
  bool operator()(clause* x, clause* y) { return x->extra.act > y->extra.act; }
};

inline void remove_watch(watch_node* watch, clause* cl) {
  // Locate the clause_head matching cl. 
  for(clause_head& elt : watch->ws) {
    if(elt.c == cl) {
      elt = watch->ws.last();
      watch->ws.pop();
      return;
    }
  }
  GEAS_ERROR;
}

inline watch_node* find_watchlist(solver_data* s, clause_elt& elt) {
#ifdef CACHE_WATCH
  assert(elt.watch);
  return elt.watch;
#else
  patom_t p(~elt.atom);
  return s->infer.get_watch(p.pid, p.val);
#endif
}

inline void detach_clause(solver_data* s, clause* cl) {
  // At least the current watches should be cached
  if(!cl->extra.one_watch) {
    /*
    assert((*cl)[0].watch);
    remove_watch((*cl)[0].watch, cl);
    */
    remove_watch(find_watchlist(s, (*cl)[0]), cl);
  }
  /*
  assert((*cl)[1].watch);
  remove_watch((*cl)[1].watch, cl);
  */
  remove_watch(find_watchlist(s, (*cl)[1]), cl);
}

inline bool is_locked(solver_data* s, clause* c) {
  int depth = c->extra.depth;
  if(s->infer.trail.size() <= depth)
    return false;

  reason& r(s->infer.trail[depth].expl);
  return r.kind == reason::R_Clause && r.cl == c;
}

void reduce_db(solver_data* s) {
  // Find the median of the clauses by activity
  vec<clause*>& learnts(s->infer.learnts);
  clause** mid = &learnts[s->learnt_dbmax/2];
  std::nth_element(learnts.begin(), mid, learnts.end(), cmp_clause_act());
  int shrunk_lits = 0;
  
  for(clause* c : range(mid, learnts.end())) {
    // If this clause is locked, we can't detach it
    if(is_locked(s, c)) {
      *mid = c; ++mid; 
      continue;
    }
    shrunk_lits += c->size();
    detach_clause(s, c);
    free(c);
  }
  int num_shrunk = learnts.end() - mid;
  s->stats.num_learnts -= num_shrunk;
  s->stats.num_learnt_lits -= shrunk_lits;
  learnts.shrink(num_shrunk);
  
  s->learnt_dbmax *= s->opts.learnt_growthrate;
}

// Pre: Conflict stuff is in 

static void clear(solver_data* s) {
  s->confl.pred_seen.clear(); 
}

// Drop a predicate from the explanation
static void remove(solver_data* s, pid_t p) {
  s->confl.pred_seen.remove(p);
  if(s->state.p_last[p] < s->confl.pred_eval[p])
    s->confl.clevel--;
  assert(!s->confl.pred_seen.elem(p));
}

#ifdef CHECK_CLEVEL
static bool is_at_current_level(solver_data* s, pid_t p, pval_t v) {
  for(int pos = s->infer.trail_lim.last(); pos < s->infer.trail.size(); ++pos) {
    if(s->infer.trail[pos].pid == p && s->infer.trail[pos].old_val < v)
      return true;
  }
  return false;
}
#endif

#ifdef CHECK_PRED_EVALS
static void check_level_preds(solver_data* s, unsigned int pos_b, unsigned int pos_e) {
  static boolset supported;
  supported.growTo(s->state.p_vals.size());

  for(int pos = pos_b; pos < pos_e; ++pos) {
    pid_t p(s->infer.trail[pos].pid);
    if(s->confl.pred_seen.elem(p) && !supported.elem(p)) {
      if(s->infer.trail[pos].old_val < s->confl.pred_eval[p]) {
        supported.add(p);
      }
    }
  }
  for(pid_t p : s->confl.pred_seen) {
    if(s->state.p_last[p] < s->confl.pred_eval[p])
      assert(supported.elem(p));
  }
  supported.clear();
}
#endif

/*
static int clevel_count(solver_data* s) {
  int c = 0;
  for(pid_t p : s->confl.pred_seen) {
    if(is_at_current_level(s, p, s->confl.pred_eval[p]))
      ++c;
  }
  return c;
}
*/


static void add(solver_data* s, clause_elt elt) {
  assert(s->state.is_inconsistent(elt.atom));
  pid_t pid = elt.atom.pid^1;
  pval_t val = pval_contra(elt.atom.val);
  assert(s->state.is_entailed(patom_t(pid, val)));
  if(!s->confl.pred_seen.elem(pid)) {
    // Not yet in the explanation
    /*
    if(s->confl.pred_saved[pid>>1].last_seen != s->confl.confl_num) {
      s->confl.pred_saved[pid>>1] = { s->confl.confl_num,
        pid&1 ? pval_inv(val) : val };
      bump_pred_act(s, pid);
    }
    */

    s->confl.pred_seen.insert(pid);
    s->confl.pred_eval[pid] = val;
#ifdef CACHE_WATCH
    s->confl.pred_hint[pid] = elt.watch;
#endif

    if(s->state.p_last[pid] < val) {
#ifdef CHECK_CLEVEL
      assert(is_at_current_level(s, pid, val));
#endif
      s->confl.clevel++;
    }
  } else {
    // Check whether the atom is already entailed.
    // pval_t val = elt.atom.val;
    pval_t e_val = s->confl.pred_eval[pid];
    if(val <= e_val) {
#ifdef CACHE_WATCH
      if(val == e_val && elt.watch)
        s->confl.pred_hint[pid] = elt.watch;
#endif
      return;
    }
    
    // Check whether this changes the current-level count
    pval_t p_last = s->state.p_last[pid];
    if(p_last < val && e_val <= p_last)
      s->confl.clevel++;

    s->confl.pred_eval[pid] = val;
#ifdef CACHE_WATCH
    s->confl.pred_hint[pid] = elt.watch;
#endif
  }
#ifdef CHECK_PRED_EVALS
  assert(s->state.is_entailed(patom_t(pid, s->confl.pred_eval[pid])));
  assert(s->confl.pred_seen.elem(pid));
#endif
}

std::ostream& operator<<(std::ostream& o, reason r) {
  o << "<- ";
  switch(r.kind) {
    case reason::R_Atom:
      o << r.at;
      break;
    case reason::R_Clause:
      {
        vec<clause_elt> es;
        auto it = r.cl->begin();
        o << "(" << *it << ")";
        for(++it; it != r.cl->end(); ++it)
          es.push(*it);
        o << es;
      }
      break;
    case reason::R_Thunk:
      {
        o << "{thunk}";
        break;
      }
    case reason::R_LE:
      {
        o << "{<=}";
        break;
      }
    case reason::R_NIL:
      {
        o << "true";
        break;
      }
    default:
      GEAS_NOT_YET;
  }
  return o;
}

// Restore solver state to a given index in the inference trail.
static inline void bt_infer_to_pos(solver_data* s, unsigned int pos) {
  pred_state& st(s->state);
  infer_info& inf(s->infer);
  for(infer_info::entry e : rev_range(&inf.trail[pos], inf.trail.end())) {
    st.p_vals[e.pid] = e.old_val; 
  }
  inf.trail.shrink_(inf.trail.size() - pos);
}

inline void apply_atom(ctx_t& ctx, patom_t at) {
  if(ctx[at.pid] < at.val)
    ctx[at.pid] = at.val;
}

bool check_inference(solver_data* s, propagator* p, patom_t z, vec<clause_elt>& expl) {
  vec<pval_t> ctx(s->state.p_root);
  apply_atom(ctx, ~z);
  for(clause_elt e : expl) {
    apply_atom(ctx, ~e.atom); 
  }
  return p->check_unsat(ctx);
}

bool check_confl(solver_data* s, propagator* p, vec<clause_elt>& expl) {
  vec<pval_t> ctx(s->state.p_root);
  for(clause_elt e : expl) {
    apply_atom(ctx, ~e.atom); 
  }
  return p->check_unsat(ctx);
}

#ifdef CHECK_EXPLNS
static bool still_entailed(solver_data* s, unsigned int pos, patom_t at) {
  pid_t p(at.pid);
  pval_t ent(at.val);
  if(s->state.p_vals[p] < ent)
    return false;
  for(; pos < s->infer.trail.size(); ++pos) {
    if(s->infer.trail[pos].pid == p)
      return s->infer.trail[pos].old_val >= ent; 
  }
  return true;
}
#endif

static forceinline void add_reason(solver_data* s, unsigned int pos, pval_t ex_val, reason r) {
  switch(r.kind) {
    case reason::R_Atom:
#ifdef PROOF_LOG
      log::add_atom(*s, r.at);
#endif
      add(s, r.at);
      break;
    case reason::R_Clause:
      {
        // Skip the first literal (which we're resolving on)
        // assert(is_locked(s, r.cl));
        bump_clause_act(s, *r.cl);
        auto it = r.cl->begin();
        for(++it; it != r.cl->end(); ++it) {
#ifdef PROOF_LOG
          log::add_atom(*s, (*it).atom);
#endif
          add(s, *it);
        }
      }
      break;
    case reason::R_LE:
      {
        // p <= q + offset.
        patom_t at(~patom_t(r.le.p, ex_val + r.le.offset));
#ifdef PROOF_LOG
        log::add_atom(*s, at);
#endif
        add(s, at);
      }
      break;
    case reason::R_Thunk:
      {
#ifdef CHECK_PRED_EVALS
        for(pid_t p : s->confl.pred_seen)
          assert(s->state.p_vals[p] >= s->confl.pred_eval[p]);
#endif
        if(r.eth.flags) {
          // Deal with Ex_BTPRED and Ex_BTGEN
          if(r.eth.flags&expl_thunk::Ex_BTPRED) {
            bt_infer_to_pos(s, pos);
#ifdef CHECK_PRED_EVALS
            for(pid_t p : s->confl.pred_seen)
              assert(s->state.p_vals[p] >= s->confl.pred_eval[p]);
#endif
          }
          if(r.eth.flags&expl_thunk::Ex_BTGEN) {
            GEAS_NOT_YET;
          }
        }
        vec<clause_elt>& es(s->confl.expl_buf); es.clear();
        r.eth(ex_val, es);
#ifdef CHECK_PRED_EVALS
        for(pid_t p : s->confl.pred_seen)
          assert(s->state.p_vals[p] >= s->confl.pred_eval[p]);
#endif
#ifdef CHECK_EXPLNS
        if(r.eth.origin) {
          for(auto at : es) {
            assert(still_entailed(s, pos, ~at.atom));
          }
          assert(check_inference(s, static_cast<propagator*>(r.eth.origin), patom_t(s->infer.trail[pos].pid, ex_val), es));
        }
#endif
        for(clause_elt e : es) {
#ifdef PROOF_LOG
          log::add_atom(*s, e.atom);
#endif
          add(s, e);
#ifdef CHECK_PRED_EVALS
          for(pid_t p : s->confl.pred_seen)
            assert(s->state.p_vals[p] >= s->confl.pred_eval[p]);
#endif
        }
      }
      break;
    case reason::R_NIL:
      break;
    default:
      GEAS_NOT_YET;
  }
}

// TODO: Fix proof logging
#if 0
static forceinline bool atom_is_redundant(solver_data* s, patom_t at) {
  pid_t pid = at.pid^1;
  pval_t val = pval_max - at.val + 1;
  assert(s->state.is_entailed(patom_t(pid, val)));
  if(!s->confl.pred_seen.elem(pid))
    return false;

  pval_t e_val = s->confl.pred_eval[pid];
  return val <= e_val;
}

static forceinline bool is_redundant(solver_data* s, reason r) {
  switch(r.kind) {
    case reason::R_Atom:
      // add(s, r.at);
      return atom_is_redundant(s, r.at);
      break;
    case reason::R_Clause:
      {
        // Skip the first literal (which we're resolving on)
        // assert(is_locked(s, r.cl));
        auto it = r.cl->begin();
        for(++it; it != r.cl->end(); ++it) {
          if(!atom_is_redundant(s, (*it).atom))
            return false;
          return true;
        }
      }
      break;
    case reason::R_LE:
      {
        // p <= q + offset.
        pval_t ex_val(s->confl.pred_eval[e.pid]);
        patom_t at(~patom_t(r.le.p, ex_val + r.le.offset));
        return atom_is_redundant(s, at);
      }
      break;
    case reason::R_Thunk:
      {
        if(r.eth.flags) {
          // If the explanation needs backtracking,
          // don't.
          return false;
        }
        vec<clause_elt>& es(s->confl.expl_buf); es.clear();
        pval_t ex_val(s->confl.pred_eval[e.pid]);
        r.eth(ex_val, es);
        for(clause_elt e : es) {
          if(!atom_is_redundant(s, e.at))
            return false;
        }
        return true;
      }
      break;
    case reason::R_NIL:
      return true;
      break;
    default:
      GEAS_NOT_YET;
  }
}
#endif

// Is the given trail entry required in the conflict?
inline bool needed(solver_data* s, infer_info::entry& entry) {
  return s->confl.pred_seen.elem(entry.pid) &&
    entry.old_val < s->confl.pred_eval[entry.pid]; 
}

inline bool l_needed(solver_data* s, persistence::pred_entry entry) {
  return s->confl.pred_seen.elem(entry.p) &&
    entry.v < s->confl.pred_eval[entry.p];
}

inline clause_elt get_clause_elt(solver_data* s, pid_t p) {
  return clause_elt(
    patom_t(p^1, pval_contra(s->confl.pred_eval[p]))
#ifdef CACHE_WATCH
    , s->confl.pred_hint[p]
#endif
  );
}

// Backtrack to the first level at which some conflict literal occurred.
// Precondition: requires conflict-analysis structures are initialised,
// but nothing at the current level.
void bt_to_clevel(solver_data* s) {
  // Dumb, but hopefully bulletproof approach: keep backtracking until we reach
  // the right level.
  int l = s->persist.pred_ltrail_lim.size()-1;
  for(pid_t pi : s->confl.pred_seen) {
    assert(s->state.p_vals[pi] >= s->confl.pred_eval[pi]);
  }
  while(l) {
    bt_to_level(s, l);
    process_initializers(*s);
    for(pid_t pi : s->confl.pred_seen) {
      if(s->state.p_last[pi] < s->confl.pred_eval[pi])
        s->confl.clevel++;
    }
    if(s->confl.clevel)
      return;
    --l;
  }
  GEAS_ERROR;
}

int compute_learnt(solver_data* s, vec<clause_elt>& confl) {
  s->confl.clevel = 0;
  s->confl.confl_num++;
  
  decay_clause_act(s);
//  std::cout << "confl:" << confl << std::endl;

  // Remember: the conflict contains things which are false.
  // The inference trail contains things which have become true.
#ifdef PROOF_LOG
  log::start_infer(*s);
#endif
  for(clause_elt e : confl) {
#ifdef PROOF_LOG
    log::add_atom(*s, e.atom);
#endif
    add(s, e);
  }
#ifdef PROOF_LOG
  log::finish_infer(*s);
#endif

  if(!s->confl.clevel) {
    // Somehow, we ended up with a conflict entirely
    // at a previous level. O__O
    bt_to_clevel(s);
  }
  assert(s->confl.clevel > 0);
  // We'll re-use confl to hold the output
  confl.clear();

//  assert(s->confl.clevel == clevel_count(s));

  // Allocate conflict for everything
  // NOTE: This should be safe, since if we're conflicting
  // there must be at least one entry on the trail.
#ifdef CHECK_PRED_EVALS
  for(pid_t p : s->confl.pred_seen)
    assert(s->state.p_vals[p] >= s->confl.pred_eval[p]);
#endif
  unsigned int pos = s->infer.trail.size()-1;
  while(!needed(s, s->infer.trail[pos])) {
    assert(pos >= 1);
    assert(pos >= s->infer.trail_lim.last());
    pos--;
  }

  infer_info::entry e(s->infer.trail[pos]);
  while(s->confl.clevel > 1) {
//    assert(s->confl.clevel == clevel_count(s));
    pval_t ex_val(s->confl.pred_eval[e.pid]);
#ifdef CHECK_PRED_EVALS
    assert(s->state.is_entailed(patom_t(e.pid, ex_val)));
#endif
    remove(s, e.pid);
#ifdef CHECK_PRED_EVALS
    for(pid_t p : s->confl.pred_seen)
      assert(s->state.p_vals[p] >= s->confl.pred_eval[p]);
#endif
#ifdef LOG_ALL
    std::cout << " <~ {" << pos << "} " << e.expl << std::endl;
#endif
#ifdef PROOF_LOG
    // Update the hint
    if(e.expl.origin != s->log.last_hint) {
      s->log.last_hint = e.expl.origin;
      fprintf(stderr, "c %d\n", e.expl.origin);
    }
    log::start_infer(*s);
    log::add_atom(*s, patom_t { e.pid, ex_val });
#endif

    add_reason(s, pos, ex_val, e.expl); 
#ifdef CHECK_PRED_EVALS
    for(pid_t p : s->confl.pred_seen)
      assert(s->state.p_vals[p] >= s->confl.pred_eval[p]);
    check_level_preds(s, s->infer.trail_lim.last(), pos);
#endif
    
#ifdef PROOF_LOG
    log::finish_infer(*s);
#endif

    assert(pos >= 1);
    assert(pos > s->infer.trail_lim.last());
    pos--;
    while(!needed(s, s->infer.trail[pos])) {
      assert(pos >= 1);
      assert(pos > s->infer.trail_lim.last());
      pos--;
    }
    e = s->infer.trail[pos];
  }
  
  // We've found the 1-UIP. Now extract the nogood.

  // e contains the asserting predicate.
  confl.push(get_clause_elt(s, e.pid));
  remove(s, e.pid);

  // Identify the backtrack level and position the
  // second watch.
  int bt_level = 0;
#if 0
  pos = s->persist.pred_ltrail.size();
  for(int l = s->persist.pred_ltrail_lim.size()-1; l > 0; l--) {
    // The awkwardness here is to avoid pos underflowing.
    while(pos > s->persist.pred_ltrail_lim[l]) {
      --pos;
      persistence::pred_entry e(s->persist.pred_ltrail[pos]);
      if(l_needed(s, e)) {
        // Literal would become unfixed at the previous level
        bt_level = l;
        confl.push(get_clause_elt(s, e.p));
        remove(s, e.p);
        goto level_found;
      }
    }
  }
#else
  // Dumb, but hopefully bulletproof approach: keep backtracking until we reach
  // the right level.
  int l = s->persist.pred_ltrail_lim.size()-1;
  for(pid_t pi : s->confl.pred_seen) {
    assert(s->state.p_vals[pi] >= s->confl.pred_eval[pi]);
  }
  while(l) {
    bt_to_level(s, l);
    process_initializers(*s);
    for(pid_t pi : s->confl.pred_seen) {
      if(s->state.p_last[pi] < s->confl.pred_eval[pi]) {
        assert(s->state.p_vals[pi] >= s->confl.pred_eval[pi]);
        bt_level = l;
        confl.push(get_clause_elt(s, pi));
        remove(s, pi);
        goto level_found;
      }
    }
    --l;
  }
#endif
#ifdef CHECK_STATE
  assert(bt_level < s->infer.trail_lim.size());
#endif
level_found:
  // Now push the remaining elts
  for(unsigned int p : s->confl.pred_seen)
    confl.push(get_clause_elt(s, p));
  clear(s);

#ifdef PROOF_LOG
  log::log_learnt(*s, confl);
#endif
 
  return bt_level;
}

bool confl_is_current(solver_data* s, vec<clause_elt>& confl) {
  if(s->persist.level() == 0)
    return true;
  for(clause_elt& e : confl) {
    if(!s->state.is_inconsistent_prev(e.atom))
      return true;
  }
  return false;
}

/*=============
 * Code for retrieving nogoods talking only about assumptions.
 *=============
 */
static inline void register_assump(solver_data& s, patom_t at) {
  if(!s.confl.pred_is_assump[at.pid]) {
    s.confl.pred_is_assump[at.pid] = true;
    s.confl.pred_assval[at.pid] = at.val;
  } else {
    s.confl.pred_assval[at.pid] = std::max(s.confl.pred_assval[at.pid], at.val);
  }
}

// Drop a predicate from the explanation
static void aconfl_remove(solver_data* s, pid_t p) {
  s->confl.pred_seen.remove(p);
  if(!s->confl.pred_is_assump[p] || s->confl.pred_assval[p] < s->confl.pred_eval[p])
    s->confl.clevel--;
  assert(s->confl.clevel >= 0);
  assert(!s->confl.pred_seen.elem(p));
}

// Is the given trail entry required in the conflict?
static inline bool aconfl_needed(solver_data* s, infer_info::entry& entry) {
  if(!s->confl.pred_seen.elem(entry.pid))
    return false;
  if(entry.old_val >= s->confl.pred_eval[entry.pid])
    return false;

  if(!s->confl.pred_is_assump[entry.pid])
    return true;
  return s->confl.pred_eval[entry.pid] > s->confl.pred_assval[entry.pid];
}


static inline void aconfl_add(solver_data* s, clause_elt elt) {
  assert(s->state.is_inconsistent(elt.atom));
  pid_t pid = elt.atom.pid^1;
  pval_t val = pval_contra(elt.atom.val);
  assert(s->state.is_entailed(patom_t(pid, val)));
  if(s->state.is_entailed_l0(patom_t(pid, val)))
    return;

  if(!s->confl.pred_seen.elem(pid)) {
    // Not yet in the explanation

    s->confl.pred_seen.insert(pid);
    s->confl.pred_eval[pid] = val;

    // Check if this is an assumption
    if(!s->confl.pred_is_assump[pid] || s->confl.pred_assval[pid] < val)
      s->confl.clevel++;
  } else {
    // Check whether the atom is already entailed.
    // pval_t val = elt.atom.val;
    pval_t e_val = s->confl.pred_eval[pid];
    if(val <= e_val) {
      return;
    }
    
    // Check whether this adds a new non-assumption
    if(s->confl.pred_is_assump[pid]) {
      // If the _pred_ isn't an assumption, it's already
      // been counted.
      if(s->confl.pred_assval[pid] < val
         && e_val <= s->confl.pred_assval[pid])
        s->confl.clevel++;
    }

    s->confl.pred_eval[pid] = val;
  }
  assert(s->state.is_entailed(patom_t(pid, s->confl.pred_eval[pid])));
  // Should be equivalent
  assert(s->state.p_vals[pid] >= s->confl.pred_eval[pid]);
  assert(s->confl.pred_seen.elem(pid));
}

static inline void aconfl_add_reason(solver_data* s, unsigned int pos, pval_t ex_val, reason r) {
  switch(r.kind) {
    case reason::R_Atom:
#ifdef PROOF_LOG
      log::add_atom(*s, r.at);
#endif
      aconfl_add(s, r.at);
      break;
    case reason::R_Clause:
      {
        // Skip the first literal (which we're resolving on)
        // assert(is_locked(s, r.cl));
        auto it = r.cl->begin();
        for(++it; it != r.cl->end(); ++it) {
#ifdef PROOF_LOG
          log::add_atom(*s, (*it).atom);
#endif
          aconfl_add(s, *it);
        }
      }
      break;
    case reason::R_LE:
      {
        // p <= q + offset.
        // TODO: Check for underflow here.
        patom_t at(~patom_t(r.le.p, ex_val + r.le.offset));
        // fprintf(stderr, "WARNING: Using R_LE.\n");
#ifdef PROOF_LOG
        log::add_atom(*s, at);
#endif
        aconfl_add(s, at);
      }
      break;
    case reason::R_Thunk:
      {
        if(r.eth.flags) {
          // Deal with Ex_BTPRED and Ex_BTGEN
          if(r.eth.flags&expl_thunk::Ex_BTPRED) {
            if(pos < s->infer.trail_lim.last()) {
              do {
                bt_to_level(s, s->infer.trail_lim.size()-1);
              } while(pos < s->infer.trail_lim.last());
              process_initializers(*s);
            }
            bt_infer_to_pos(s, pos);
          }
          if(r.eth.flags&expl_thunk::Ex_BTGEN) {
            GEAS_NOT_YET;
          }
        }
        vec<clause_elt>& es(s->confl.expl_buf); es.clear();
        r.eth(ex_val, es);
#ifdef CHECK_EXPLNS
        if(r.eth.origin) {
          for(auto at : es) {
            assert(still_entailed(s, pos, ~at.atom));
          }
          assert(check_inference(s, static_cast<propagator*>(r.eth.origin), patom_t(s->infer.trail[pos].pid, ex_val), es));
        }
#endif
        for(clause_elt e : es) {
#ifdef PROOF_LOG
          log::add_atom(*s, e.atom);
#endif
          aconfl_add(s, e);
        }
      }
      break;
    case reason::R_NIL:
      GEAS_ERROR;
      break;
    default:
      GEAS_NOT_YET;
  }
}

void retrieve_assumption_nogood(solver_data* s, vec<patom_t>& confl) {
  // Have to use separate structures for data, because
  // s.wake_vals and s.pred_queued get reset during backtracking.
  confl.clear();
  if(!s->solver_is_consistent)
    return;
  s->confl.clevel = 0;
  s->confl.pred_is_assump.growTo(s->wake_vals.size(), false);
  s->confl.pred_assval.growTo(s->wake_vals.size(), 0);

  unsigned int end = s->last_confl.assump_idx;
  for(int ai = 0; ai < end; ai++) {
    register_assump(*s, s->assumptions[ai]);
  }
   
  switch(s->last_confl.kind) {
    case C_Infer:
      for(clause_elt& e : s->infer.confl) {
        assert(s->state.is_inconsistent(e.atom));
        aconfl_add(s, e);
      }
      break;
    case C_Assump:
      {
        // Weaken the failed assumption.
        // patom_t at = s->assumptions[s->last_confl.assump_idx];
        pid_t pid = s->assumptions[s->last_confl.assump_idx].pid;
        patom_t at(pid, pval_contra(s->state.p_vals[pid^1]));
        aconfl_add(s, at);
        confl.push(~at);
      }
      break;
    default:
      GEAS_ERROR;
  }


#if 0
  // WARNING: This runs into troubles if late
  // variables, which have an incomplete history,
  // need to be explained at an earlier level.
  unsigned int pos = s->infer.trail.size()-1;
  while(s->confl.clevel > 0) {
    while(!aconfl_needed(s, s->infer.trail[pos])) {
      assert(pos >= 1);
      pos--;
    }
    infer_info::entry e(s->infer.trail[pos]);

    pval_t ex_val(s->confl.pred_eval[e.pid]);
    assert(s->state.is_entailed(patom_t(e.pid, ex_val)));
    aconfl_remove(s, e.pid);

    aconfl_add_reason(s, pos, ex_val, e.expl);
    --pos;
  }
#else
  // This alternate approach should be bulletproof.
  if(s->confl.clevel > 0) {
    int l = s->infer.trail_lim.size();
    do {
      unsigned int pos = s->infer.trail.size()-1;
      unsigned int top = s->infer.trail_lim.last();
      for(; pos > top; --pos) {
        if(!aconfl_needed(s, s->infer.trail[pos]))
          continue;
        infer_info::entry e(s->infer.trail[pos]);

        pval_t ex_val(s->confl.pred_eval[e.pid]);
        assert(s->state.is_entailed(patom_t(e.pid, ex_val)));
        aconfl_remove(s, e.pid);
        aconfl_add_reason(s, pos, ex_val, e.expl);
        if(!s->confl.clevel)
          goto assumption_finished;
      }
      if(pos == top) {
        assert(!aconfl_needed(s, s->infer.trail[pos]));
      }

      --l;
      bt_to_level(s, l);
      process_initializers(*s);

    } while(l >= 0);
  }
assumption_finished:
#endif
  
  // Now collect the conflict
  for(unsigned int p : s->confl.pred_seen) {
    assert(s->confl.pred_is_assump[p]);
    confl.push(get_clause_elt(s, p).atom);
  }
    
  // And clean up the solver state
  clear(s);

  // Explanations may have backtracked
  unsigned int lev = s->infer.trail_lim.size();
  for(; lev > 0 && s->infer.trail_lim[lev-1] <= s->infer.trail.size(); --lev)
    continue;

  if(lev < s->infer.trail_lim.size())
    bt_to_level(s, lev);

  for(patom_t at : s->assumptions) 
    s->confl.pred_is_assump[at.pid] = false;
  // assert(s->pred_queue.size() == 0);
  
  /*
  fprintf(stderr, "retrieved: [|");
  for(patom_t at : confl) {
    if(at.pid&1) {
      fprintf(stderr, "p%d <= %lld;", at.pid>>1, to_int(pval_inv(at.val)));
    } else {
      fprintf(stderr, "p%d >= %lld;", at.pid>>1, to_int(at.val));
    }
  }
  fprintf(stderr, "|]\n");
  */
}

}
