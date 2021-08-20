#include <stdint.h>
#include <geas/utils/defs.h>
#include <geas/engine/geas-types.h>
#include <geas/solver/solver_data.h>
#include <geas/engine/persist.h>

namespace geas {

void push_level(solver_data* s) {
  persistence& p(s->persist);

  s->infer.trail_lim.push(s->infer.trail.size());

  // p.bvar_trail_lim.push(p.bvar_trail.size());
  p.dtrail_lim.push(p.data_trail.size());

  p.pwatch_lim.push(p.pwatch_trail.size());

  p.pred_ltrail_lim.push(p.pred_ltrail.size());
  for(pid_t pi : p.touched_preds) {
    p.pred_touched[pi] = false;
    persistence::pred_entry e = { pi, s->state.p_last[pi] };
    s->state.p_last[pi] = s->state.p_vals[pi];
    p.pred_ltrail.push(e);
  }
  p.touched_preds.clear();

  for(char* c : p.reset_flags)
    *c = false;
  p.reset_flags.clear();
  
  p.expl_trail_lim.push(p.expl_trail.size());
}

// Doesn't call destructors
template<class T>
inline void dropTo_(vec<T>& v, int sz) {
  v.shrink_(v.size() - sz);
}

inline void restore_data_elt(solver_data* s, persistence::data_entry e) {
  switch(e.sz) {
    case 1:
      *((uint8_t*) e.ptr) = ((uint8_t) e.val);
      break;
    case 2:
      *((uint16_t*) e.ptr) = ((uint16_t) e.val);
      break;
    case 4:
      *((uint32_t*) e.ptr) = ((uint32_t) e.val); 
      break;
    default:
      *((uint64_t*) e.ptr) = ((uint64_t) e.val);
  }
}

inline void bt_data(solver_data* s, unsigned int l) {
  persistence& p(s->persist);
  assert(l < p.dtrail_lim.size());

  unsigned int p_lim = p.dtrail_lim[l];
  for(auto e : rev_range(&p.data_trail[p_lim], p.data_trail.end()))
    restore_data_elt(s, e);
  dropTo_(p.data_trail, p_lim);
  dropTo_(p.dtrail_lim, l);
}

void bt_data_to_pos(solver_data* s, unsigned int p_lim) {
  persistence& p(s->persist);
  assert(p_lim >= p.dtrail_lim.last());
  for(auto e : rev_range(&p.data_trail[p_lim], p.data_trail.end()))
    restore_data_elt(s, e);
  dropTo_(p.data_trail, p_lim);
}

inline void bt_explns(solver_data* s, unsigned int l) {
  persistence& p(s->persist);
  unsigned int e_lim = p.expl_trail_lim[l];
  for(clause* c : rev_range(&p.expl_trail[e_lim], p.expl_trail.end()))
    // delete c;
    free(c);
  dropTo_(p.expl_trail, e_lim);
  dropTo_(p.expl_trail_lim, l); 
}

// inline
void bt_preds(solver_data* s, unsigned int l) {
  pred_state& st(s->state);
  persistence& p(s->persist);
  infer_info& inf(s->infer);

  // Don't use the implication graph for restoration;
  // use pred_ltrail instead.
  assert(l < inf.trail_lim.size());
  dropTo_(inf.trail, inf.trail_lim[l]);
  dropTo_(inf.trail_lim, l);
  
  assert(l < p.pred_ltrail_lim.size());
  // If solving was interrupted, things in the prop
  // and wake queue may not recognized as touched.
  while(!s->pred_queue.empty()) {
    pid_t pi = s->pred_queue._pop();
    s->pred_queued[pi] = false;
    st.p_vals[pi] = st.p_last[pi]; 
  }
  for(pid_t pi : s->wake_queue) {
    s->wake_queued[pi] = false;
    st.p_vals[pi] = st.p_last[pi];
  }
  s->wake_queue.clear();

  // Reset preds touched at the current level
#if 1
  for(pid_t pi : p.touched_preds) {
    p.pred_touched[pi] = false;
    st.p_vals[pi] = st.p_last[pi];
  }
  p.touched_preds.clear();

  // Now walk through the history, walking back p_vals
  // and p_last in lockstep.
  int p_lim = p.pred_ltrail_lim[l];
  int p_end = p.pred_ltrail.size();
  // Rewind all but the most recent level
  for(int lev = p.pred_ltrail_lim.size()-1; lev > l; --lev) {
    int p_mid = p.pred_ltrail_lim[lev];
    for(auto e : range(p.pred_ltrail + p_mid, p.pred_ltrail + p_end)) {
      st.p_vals[e.p] = e.v;
      st.p_last[e.p] = e.v;
    }
    p_end = p_mid;
  }
  // For the last level, also restore the 'touched' markers.
  for(auto e : range(p.pred_ltrail + p_lim, p.pred_ltrail + p_end)) {
    p.pred_touched[e.p] = true;
    p.touched_preds.push(e.p);
    st.p_vals[e.p] = st.p_last[e.p];
    s->wake_vals[e.p] = st.p_last[e.p];
    st.p_last[e.p] = e.v;
  }
#else
  // This is slightly wasteful. Figure out a better way.
  int p_lim = p.pred_ltrail.size();
  for(int lev = p.pred_ltrail_lim.size()-1; lev >= ((int) l); lev--) {
    for(pid_t pi : p.touched_preds) {
      p.pred_touched[pi] = false;
      st.p_vals[pi] = st.p_last[pi];
    }
    p.touched_preds.clear();

    int p_start = p.pred_ltrail_lim[lev]; 
    for(auto e : range(&p.pred_ltrail[p_start], &p.pred_ltrail[p_lim])) {
      p.pred_touched[e.p] = true;
      p.touched_preds.push(e.p);
      st.p_vals[e.p] = st.p_last[e.p];
      st.p_last[e.p] = e.v;
    }
    p_lim = p_start;
  }
#endif
  dropTo_(p.pred_ltrail, p_lim);
  dropTo_(p.pred_ltrail_lim, l);

  // Update the watch heads
  unsigned int pw_lim = p.pwatch_lim[l];
  for(auto e : rev_range(&p.pwatch_trail[pw_lim], p.pwatch_trail.end()))
    s->infer.pred_watches[e.p] = e.node;
  dropTo_(p.pwatch_trail, pw_lim);
  dropTo_(p.pwatch_lim, l);
}

void pop_level(solver_data* s) {
  bt_to_level(s, s->infer.trail_lim.size()-1);
}

void check_at_fixpoint(solver_data* s) {
  assert(s->pred_queue.empty());
  assert(s->wake_queue.size() == 0);
  // assert(s->prop_queue.empty());  
  assert(!s->queue_has_prop);
  for(int p = 0; p < PRIO_LEVELS; ++p)
    assert(s->prop_queue[p].empty());  
}

void bt_to_level(solver_data* s, unsigned int l) {
  // Three components of state:
  // predicates, explanations, and opaque data
#ifdef CHECK_STATE
  check_at_fixpoint(s);
#endif
  // Reset flags.
  for(char* c : s->persist.bt_flags)
    *c = false;
  s->persist.bt_flags.clear();

  for(char* c : s->persist.reset_flags)
    *c = false;
  s->persist.reset_flags.clear();

  // Deal with current and last-level pred values
  bt_preds(s, l);

  // Restore other assorted data
  bt_data(s, l);

  // Collect temporary explanations
  bt_explns(s, l); 
}

}
