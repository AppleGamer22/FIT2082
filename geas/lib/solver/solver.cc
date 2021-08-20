#include <iostream>
#include <algorithm>
#include <csignal>
#include <climits>
#include <math.h>
#include <geas/solver/solver.h>
#include <geas/solver/solver_data.h>
#include <geas/solver/solver_debug.h>
#include <geas/solver/stats.h>
#include <geas/solver/options.h>
#include <geas/engine/conflict.h>

// Suppress inlining, for profiling
// #define INLINE_ATTR __attribute__((noinline))
// #define INLINE_SATTR INLINE_ATTR

//#define INLINE_ATTR forceinline
//#define INLINE_SATTR static INLINE_ATTR

#define KEEP_GLUE
// #define RESTART_LUBY

// Default options
options default_options = {
  // 50000, // int learnt_dbmax; 
  10000, // int learnt_dbmax; 
  1.02, // double learnt_growthrate;

  0.01, // double pred_act_inc;
  1.05, // double pred_act_growthrate; 

  1, // double learnt_act_inc;
  1.001, // double learnt_act_growthrate;

  1000, // int restart_limit;
  1.05, // double restart_growthrate;

  1,     // one_watch
  0,     // global_diff

//  200, // eager_threshold
   10, // eager_threshold
};

limits no_limit = {
  0,
  0
};

using std::cout;
using std::cerr;
using std::endl;
using std::min;
using std::max;
using std::sort;

#ifdef LOG_RESTART
static double domains_total = 0;
#endif

namespace geas {

/* This flag controls early solver termination */
volatile static sig_atomic_t global_abort = 0;

/* The signal handler just sets the flag. Now _doesn't_
 * re-enable itself. */
void catch_int (int sig) {
  global_abort = 1;
  // signal (sig, catch_int);
}
void set_handlers(void) {
  signal(SIGINT, catch_int);
}
void clear_handlers(void) {
  signal(SIGINT, SIG_DFL);
}

pval_t patom_t::val_max = pval_max;

typedef solver_data sdata;

// #define MANAGERS_MAX 10
struct man_template_t {
  void* (*create)(solver_data* s);
  void (*destroy)(void*);
};
struct man_list_t {
  man_template_t m;
  man_list_t* tl;
};
// static man_template_t man_registry[MANAGERS_MAX];
struct man_registry {
  unsigned int sz; 
  man_list_t* l;
};

/*
static unsigned int& man_sz(void) {
  static unsigned int sz = 0;
  return sz;
}
*/
static man_registry& get_reg(void) {
  static man_registry r { 0, nullptr };
  return r;
}

man_id_t register_manager(void* (*create)(solver_data* s), void (*destroy)(void*)) {
  /*
  if(man_sz() >= MANAGERS_MAX) {
    fprintf(stderr, "ERROR: Registering too many managers. Increase MANAGERS_MAX and recompile.\n");
    GEAS_ERROR;
  }
  man_registry[man_sz()++] = man_template_t { create, destroy };
  */
  man_registry& r(get_reg());
  man_id_t id = r.sz++;
  r.l = new man_list_t { man_template_t { create, destroy }, r.l };
  return id;
}

solver::solver(void)
  : data(new solver_data(default_options))
//  , ivar_man(data)
  {
   
}

solver::~solver(void) {
  // Free propagators
  delete data;
}

solver::solver(options& _opts)
  : data(new solver_data(_opts))
//  , ivar_man(data)
  {

}

void save_model_vals(void* ptr) {
  solver_data* s(static_cast<solver_data*>(ptr));
  
  for(int p = 0; p < s->state.p_vals.size(); p += 2) {
    s->confl.pred_saved[p>>1].val = s->state.p_vals[p];
    if(s->polarity[p>>1].has_preference)
      s->polarity[p>>1].branch = s->polarity[p>>1].preferred;
  }
}
 
solver_data::solver_data(const options& _opts)
    : opts(_opts),
      stats(),
      active_prop(nullptr),
      last_branch(default_brancher(this)), 
      pred_heap(act_cmp { infer.pred_act }),
      queue_has_prop(0),
      // Assumption handling
      assump_end(0),
      init_end(0), init_saved(0),
      // Dynamic parameters
      learnt_act_inc(opts.learnt_act_inc),
      pred_act_inc(opts.pred_act_inc),
      learnt_dbmax(opts.learnt_dbmax),
      abort_solve(0),
      solver_is_consistent(1) {
  new_pred(*this, 0, 0);
  man_registry& r(get_reg());
  managers.growTo(r.sz, manager_t { nullptr, nullptr });
  unsigned int idx = r.sz-1;
  for(man_list_t* hd = r.l; hd != nullptr; hd = hd->tl, --idx) {
    // man_template_t m = man_registry[mi]; 
    man_template_t m = hd->m;
    // managers.push(manager_t { m.create(this), m.destroy });
    managers[idx] = manager_t { m.create(this), m.destroy };
  }

  on_solution.push(event_callback { save_model_vals, this });
}

solver_data::~solver_data(void) {
  for(propagator* p : propagators)
    delete p;
  for(brancher* b : branchers)
    delete b;
  for(auto m : managers)
    m.destroy(m.ptr);

  assert(last_branch);
  delete last_branch;
}

intvar solver::new_intvar(intvar::val_t lb, intvar::val_t ub) {
  return get_ivar_man(data)->new_var(lb, ub);
}
fp::fpvar solver::new_floatvar(fp::val_t lb, fp::val_t ub) {
  return fp::get_man(data)->new_var(lb, ub);
}

patom_t solver::new_boolvar(void) { return new_bool(*data); }

// For debugging
std::ostream& operator<<(std::ostream& o, const patom_t& at) {
  if(at.pid&1) {
    o << "p" << (at.pid>>1) << " <= " << to_int(pval_inv(at.val));
  } else {
    o << "p" << (at.pid>>1) << " >= " << to_int(at.val);
  }
  return o;
}
std::ostream& operator<<(std::ostream& o, const clause_elt& e) {
  o << e.atom;
  return o;
}

struct stat_reporter {
  stat_reporter(solver_data* _s)
    : s(_s) { }

  ~stat_reporter(void) {
    for(propagator* p : s->propagators) {
      p->report_internal(); 
    }
  }
  solver_data* s;
};

// Record that the value of p has changed at the
// current decision level.
INLINE_SATTR void touch_pred(solver_data& s, pid_t p) {
  if(!s.persist.pred_touched[p]) {
    s.persist.pred_touched[p] = true;
    s.persist.touched_preds.push(p);
    s.wake_vals[p] = s.state.p_last[p];
  }
}

// inline bool is_bool(sdata& s, pid_t p) { return s.state.pred_is_bool(p); }
// inline bool is_bool(sdata& s, pid_t p) { return false; }

inline int decision_level(sdata& s) {
  return s.infer.trail_lim.size();
}

static pid_t alloc_pred(sdata& s, pval_t lb, pval_t ub, unsigned char flags) {
#ifdef LOG_RESTART
  domains_total += (ub - lb);
#endif

  s.pred_callbacks.push();
  s.pred_callbacks.push();

  s.pred_queued.push(false);
  s.pred_queued.push(false);

  s.pred_origin.push(nullptr);
  s.pred_origin.push(nullptr);
    
  s.wake_queued.push(false);
  s.wake_queued.push(false);
  s.wake_vals.push(lb);
  s.wake_vals.push(pval_inv(ub));

  s.state.new_pred(lb, ub);
  s.persist.new_pred();
  s.confl.new_pred();
  // pid_t pi = s.infer.new_pred();
  pid_t pi = s.infer.new_pred(lb, ub);

  // s.pred_heap.insert(pi);
  // s.pred_heap.insert(pi+1);
  if(!(flags&PR_NOBRANCH))
    s.pred_heap.insert(pi>>1);

  s.polarity.push();
  
  queue_pred(&s, pi);
  queue_pred(&s, pi^1);

  return pi;  
}

pid_t new_pred(sdata& s, pval_t lb, pval_t ub, unsigned char flags) {
  // assert(decision_level(s) == 0);
  pid_t p = alloc_pred(s, lb, ub, flags);

  run_callbacks(s.on_pred);

  return p;
}

void push_init(sdata& s, pinit_data d) {
  assert(s.init_end == s.initializers.size());
  trail_save(s.persist, s.init_end, s.init_saved);
  s.initializers.push(d); 
  s.init_end++; 
}
/*
void initialize(pid_t p, pred_init init, vec<pval_t>& vals) {
  pred_init::prange_t r(init(vals));
  vals[p] = r[0];
  vals[p+1] = r[1];
}
*/

pid_t new_pred(sdata& s, pred_init init_lb, pred_init init_ub, unsigned char flags) {
  pval_t lb_0 = init_lb(s.state.p_root);
  pval_t inv_ub_0 = init_ub(s.state.p_root);

  pid_t p = alloc_pred(s, lb_0, pval_inv(inv_ub_0), flags);
  // Set up the prev and current values
  // Root values are set up during allocation
  s.state.p_last[p] = init_lb(s.state.p_last);
  s.state.p_last[p^1] = init_ub(s.state.p_last);
    
  pval_t lb = init_lb(s.state.p_vals);
  pval_t ub = init_ub(s.state.p_vals);

  s.state.p_vals[p] = lb;
  s.state.p_vals[p^1] = ub;

  assert(s.init_end == s.initializers.size());
  if(lb != lb_0) {
    // s.initializers.push(pinit_data {p, init_lb} ); 
    // s.init_end++;
    push_init(s, pinit_data { p, init_lb });
    if(lb != s.state.p_last[p]) {
      infer_info::entry e = { p, s.state.p_last[p], init_lb.expl() };
      s.infer.trail.push(e);
      // s.persist.pred_ltrail.push(persistence::pred_entry {p, last});
      touch_pred(s, p);
    }
  }

  if(ub != inv_ub_0) {
    // s.initializers.push(pinit_data {p^1, init_ub} ); 
    // s.init_end++;
    push_init(s, pinit_data { p^1, init_ub });
    if(ub != s.state.p_last[p^1]) {
      infer_info::entry e = { p^1, s.state.p_last[p^1], init_ub.expl() };
      s.infer.trail.push(e);
      // s.persist.pred_ltrail.push(persistence::pred_entry {p^1, last});
      touch_pred(s, p);
    }
  }

  run_callbacks(s.on_pred);

  return p;
}

pval_t init_bool_lb(void* ptr, int eid, vec<pval_t>& vals) {
  return from_int(0);
}
pval_t init_bool_ub(void* ptr, int eid, vec<pval_t>& vals) {
  return pval_inv(from_int(1));
}

/*
pred_init::prange_t init_bool(void* ptr, int eid, vec<pval_t>& vals) {
  // return pred_init::prange_t { {0, pval_max - 1} };
  return pred_init::prange_t { {from_int(0), pval_max - from_int(1)} };
}
*/

patom_t new_bool(sdata& s, pred_init init_lb, pred_init init_ub) {
  pid_t pi(new_pred(s, init_lb, init_ub));
  return patom_t(pi, from_int(1));
}

patom_t new_bool(sdata& s) {
  // return new_bool(s, pred_init(init_bool, nullptr, 0));
  pid_t pi(new_pred(s, from_int(0), from_int(1)));
  return patom_t(pi, from_int(1));
}

void process_initializers(solver_data& s) {
  if(s.init_end != s.initializers.size()) {
    trail_save(s.persist, s.init_end, s.init_saved);
    vec<pinit_data>& inits(s.initializers);
    unsigned int& end = s.init_end;

    for(int ii = end; ii != inits.size(); ++ii) {
      pid_t p(inits[ii].pi); 
      pval_t curr = inits[ii].init(s.state.p_vals);
//      assert(curr == s.state.p_last[p]);
      pval_t last = inits[ii].init(s.state.p_last);
      s.state.p_last[p] = last;
      s.state.p_vals[p] = curr;
      s.wake_vals[p] = curr;

      if(curr != last) {
        infer_info::entry e = { p, last, inits[ii].init.expl() };
        s.infer.trail.push(e);
        // Shouldn't be needed, because the initializer will be called again.
        // s.persist.pred_ltrail.push(persistence::pred_entry {p, last});
        touch_pred(s, p);
      }

      // If this is at its initial value, discard it.
      if(curr != s.state.p_root[p]) {
        inits[end++] = inits[ii];
      } else {
        inits[ii].init.finalize(&s);
      }
    }
    inits.shrink_(inits.size() - end);
  }
}


void set_confl(sdata& s, patom_t p, reason r, vec<clause_elt>& confl) {
  confl.clear();

  switch(r.kind) {
    case reason::R_Atom:
      confl.push(p);
      confl.push(r.at);
      break;
    case reason::R_Clause:
      confl.push(p);
      for(clause_elt e : r.cl->tail())
        confl.push(e);
       break;
     case reason::R_Thunk:
     {
       // pval_t fail_val = pval_max - s.state.p_vals[p.pid^1] + 1;
       pval_t fail_val = pval_contra(s.state.p_vals[p.pid^1]);
       // pval_t fail_val = p.val;
       assert(fail_val <= p.val);
       confl.push(patom_t {p.pid, fail_val});
       r.eth(fail_val, confl);
       break;
     }
     case reason::R_LE:
     {
       confl.push(p);
        patom_t at(~patom_t(r.le.p, p.val + r.le.offset));
        confl.push(at);
        break;
     }
     case reason::R_NIL:
      assert(decision_level(s) == 0);
      return;
     default:
       GEAS_NOT_YET;
  }

  // Check that there's something at the current level.
retry_level:
#ifdef CHECK_STATE
  for(clause_elt& e : confl) {
    assert(s.state.is_inconsistent(e.atom));
  }
#endif
  for(clause_elt& e : confl) {
    if(!s.state.is_inconsistent_prev(e.atom))
      return;
  }
  // Nothing at the current level: find the appropriate level.
//  GEAS_ERROR;
  int level = s.persist.level();
  if(level > 0) {
    bt_to_level(&s, level-1);
    process_initializers(s);
    goto retry_level;
  }
}

inline bool is_entailed(sdata& s, patom_t p) { return s.state.is_entailed(p); }
inline bool is_inconsistent(sdata& s, patom_t p) { return s.state.is_inconsistent(p); }

bool solver::post(patom_t p) {
  if(decision_level(*data) > 0)
    bt_to_level(data, 0); 
  if(is_inconsistent(*data, p)) {
    data->solver_is_consistent = false;
    data->last_confl = { C_Infer, 0 };
    return false;
  }
  return enqueue(*data, p, reason());
}

void clear_reset_flags(solver_data& s) {
  for(char* c : s.persist.reset_flags)
    *c = 0;
  s.persist.reset_flags.clear();
}

inline void simplify_at_root(solver_data& s);

// TODO: Implement timing properly.
#include <ctime>
#include <sys/time.h>
#include <unistd.h>
static double getTime(void) {
  struct timeval t;
  gettimeofday(&t, NULL);
  return t.tv_sec + ((double) t.tv_usec)/1e6;
}

struct stat_recorder {
  stat_recorder(solver_data* _s)
    : s(_s), start_time(getTime()), confl_num(0)  { }

  ~stat_recorder(void) {
    s->stats.conflicts += confl_num;
    s->stats.time += getTime() - start_time;
  }

  void conflict(void) { ++confl_num; }

  solver_data* s;
  double start_time;
  unsigned int confl_num;
};

INLINE_SATTR bool propagate_assumps(solver_data& s) {
  s.infer.confl.clear();
#ifdef REPORT_INTERNAL_STATS
  stat_reporter rp(&s);
#endif
  stat_recorder rec(&s);
  
  if(!s.solver_is_consistent)
    return false;

  int idx = s.assump_end;

  process_initializers(s);

  if(!propagate(s)) {
    if(idx == 0)
      s.solver_is_consistent = false;
    s.last_confl = { C_Infer, idx };
    return false;
  }
  if(decision_level(s) == 0)
    simplify_at_root(s);

  for(; idx < s.assumptions.size(); ++idx) {
    s.assump_level[idx] = decision_level(s);
    patom_t at(s.assumptions[idx]);
    if(is_entailed(s, at))
      continue;

    if(is_inconsistent(s, at)) {
      s.last_confl = { C_Assump, idx };
      rec.conflict();
      return false;
    }
    
    // Otherwise, push a new level and propagate
    // the assumption.
    push_level(&s);
    trail_change(s.persist, s.assump_end, idx+1);
    if(!enqueue(s, at, reason())) {
      // Should be unreachable
      GEAS_ERROR;
      rec.conflict();
      return false;
    }

    s.infer.confl.clear();
    if(!propagate(s)) {
      s.last_confl = { C_Infer, idx+1 };
      rec.conflict();
      return false;
    }
  }

  return true;
}

bool solver::is_consistent(void) {
  solver_data& s(*data);
  if(s.assump_end == s.assumptions.size()) {
    // Backtrack to the end of assumptions
    if(s.assump_level.size() > 0 &&
      s.assump_level.last()+1 < decision_level(s)) {
      bt_to_level(&s, s.assump_level.last()+1);
      return s.solver_is_consistent && propagate(s);
    }
  }
  return propagate_assumps(s);
}

bool solver::assume(patom_t p) {
#ifdef LOG_ALL
  cerr << "+ [" << p << "]" << endl;
#endif
  if(data->assump_end == data->assumptions.size()) {
    int lev = (data->assump_end > 0)
      ?  data->assump_level.last() + 1 : 0;
    if(decision_level(*data) > lev)
      bt_to_level(data, lev);
  }
  data->assumptions.push(p);
  data->assump_level.push(0);

  return propagate_assumps(*data);
  /*
  if(data->state.is_entailed(p))
    return true;

  push_level(&s);
  if(!enqueue(*data, p, reason()))
    return false;
  trail_change(data->persist, data->assump_start, assumptions.size());
  return propagate(*data);
  */
  return true;
}

bool solver::assume(patom_t* b, patom_t* e) {
  push_assump_ctx();
  /*
  for(; b != e; ++b) {
    if(!assume(*b))
      return false;
  }
  */
  if(data->assump_end == data->assumptions.size()) {
    if(data->assump_end == data->assumptions.size()) {
      int lev = data->assumptions.size() > 0 ? data->assump_level.last() + 1 : 0;
      if(decision_level(*data) > lev)
        bt_to_level(data, lev);
    }
  }
  for(; b != e; ++b) {
    data->assumptions.push(*b);
    data->assump_level.push(0); 
  }
  return propagate_assumps(*data);
}

void solver::retract(void) {
  // Make sure the current assumption is un-queued.
  assert(data->assumptions.size() > 0);
  if(data->assump_end == data->assumptions.size()) { 
    bt_to_level(data, data->assump_level.last());
  }
  assert(data->assump_end <= data->assumptions.size());

  data->assumptions.pop();
  data->assump_level.pop();

  return; 
}

// Push an assumption context (not a decision level)
void solver::push_assump_ctx(void) {
  data->assump_ctx_lim.push(data->assumptions.size());
}

void solver::pop_assump_ctx(void) {
  if(data->assump_ctx_lim.size() > 0) {
    int lim = data->assump_ctx_lim.last(); 
    data->assump_ctx_lim.pop();

    if(data->assump_end > lim) {
      bt_to_level(data, data->assump_level[lim]);
    }
    assert(data->assump_end <= lim);
    data->assumptions.shrink_(data->assumptions.size()-lim);
    data->assump_level.shrink_(data->assump_level.size()-lim);
  } else {
    if(data->assump_end > 0)
      bt_to_level(data, 0);
    data->assumptions.clear();
    data->assump_level.clear();
  }
}

void solver::clear_assumptions(void) {
#ifdef LOG_ALL
  cerr << "_|_" << endl;
#endif
  if(decision_level(*data) > 0)
    bt_to_level(data, 0);
  data->assumptions.clear();
  data->assump_level.clear();
  data->assump_ctx_lim.clear();
  data->assump_end = 0;
}

void solver::restart(void) {
  if(decision_level(*data) > 0)
    bt_to_level(data, 0);
}

void solver::backtrack(void) {
  if(decision_level(*data) > 0) {
    bt_to_level(data, decision_level(*data)-1);
    process_initializers(*data);
  }
}

unsigned int solver::level(void) const {
  return decision_level(*data);
}

#ifdef LOG_RESTART
static int num_props = 0;
#endif

// static 
bool _enqueue(sdata& s, patom_t p, reason r) {
#ifdef LOG_ALL
  cout << "|- " << p << "{" << s.infer.trail.size() << "}" << endl;
#endif

  /*
  assert(p.pid < s.pred_queued.size());
  // assert(!s.state.is_entailed(p));
  if(s.state.is_entailed(p))
    return true;
    */

#ifdef LOG_RESTART
  num_props++;
#endif

  pval_t old_val = s.state.p_vals[p.pid];
  if(!s.state.post(p)) {
    // Setup conflict
    set_confl(s, p, r, s.infer.confl); 
    return false;
  }
  s.pred_origin[p.pid] = s.active_prop;

  if(r.kind == reason::R_Clause)
    r.cl->extra.depth = s.infer.trail.size();

  // infer_info::entry e = { p.pid, old_val, r };
  // s.infer.trail.push(e);
  s.infer.trail.push(infer_info::entry { p.pid, old_val, r });
#ifdef PROOF_LOG
  // e.expl.origin = s.log.active_constraint;
  s.infer.trail.last().expl.origin = s.log.active_constraint;
#endif
  if(!s.pred_queued[p.pid]) {
    s.pred_queue.insert(p.pid);
    s.pred_queued[p.pid] = true;
  }

  return true;
}

// Modifies elt.watch;
INLINE_SATTR vec<clause_head>& find_watchlist(solver_data& s, clause_elt& elt) {
  // Find the appropriate watch_node.
#ifdef CACHE_WATCH
  if(elt.watch) {
#ifdef DEBUG_WMAP
    assert(elt.watch->curr_val == ~(elt.atom).val);
#endif
    return elt.watch->ws;
  }
#endif

  patom_t p(~elt.atom);
  watch_node* watch = s.infer.get_watch(p.pid, p.val);
#ifdef DEBUG_WMAP
  assert(watch->curr_val == ~(elt.atom).val);
#endif
#ifdef CACHE_WATCH
  elt.watch = watch;
#endif
  return watch->ws;
}

/* static */
__attribute__((noinline)) vec<clause_head>& lookup_watchlist(solver_data& s, clause_elt& elt) {
  // Find the appropriate watch_node.
#ifdef CACHE_WATCH
  if(elt.watch) {
#ifdef DEBUG_WMAP
    assert(elt.watch->curr_val == ~(elt.atom).val);
#endif
    return elt.watch->ws;
  }
#endif

  patom_t p(~elt.atom);
  watch_node* watch = s.infer.lookup_watch(p.pid, p.val);
#ifdef DEBUG_WMAP
  assert(watch->curr_val == ~(elt.atom).val);
#endif
#ifdef CACHE_WATCH
  elt.watch = watch;
#endif
  return watch->ws;
}


/* static */
__attribute__((noinline)) vec<patom_t>& find_bin_watchlist(solver_data& s, clause_elt& elt) {
  // Find the appropriate watch_node.
#ifdef CACHE_WATCH
  if(elt.watch) {
#ifdef DEBUG_WMAP
    assert(elt.watch->curr_val == ~(elt.atom).val);
#endif
    return elt.watch->bin_ws;
  }
#endif

  patom_t p(~elt.atom);
  watch_node* watch = s.infer.get_watch(p.pid, p.val);
#ifdef DEBUG_WMAP
  assert(watch->curr_val == ~(elt.atom).val);
#endif
#ifdef CACHE_WATCH
  elt.watch = watch;
#endif
  return watch->bin_ws;
}

INLINE_SATTR
bool update_watchlist(solver_data& s,
    clause_elt elt, vec<clause_head>& ws) {
#ifdef CHECK_STATE
  assert(s.state.is_inconsistent(elt.atom));
#endif
  int jj = 0;
  int ii;
  for(ii = 0; ii < ws.size(); ii++) {
    clause_head& ch = ws[ii];
    if(s.state.is_entailed(ch.e0)) {
      // If the clause is satisfied, just
      // copy the watch and keep going;
      ws[jj++] = ch;
      continue;
    }

    /*
    if(!ch.c) {
      // Binary clause.
      if(!enqueue(s, ch.e0, elt.atom)) {
        // Copy remaining watches and signal conflict.
        for(; ii < ws.size(); ii++)
          ws[jj++] = ws[ii];
        ws.shrink(ii-jj);
        return false;
      }
      ws[jj++] = ch;
      continue;
    }
    */
    // Normal case: look for a new watch
    clause& c(*ch.c);
    // if(c[1].atom != elt.atom) {
    if(c[1].atom.pid != elt.atom.pid) {
#ifdef CACHE_WATCH
      elt.watch = c[0].watch;
#endif
      c[0] = c[1];
    } else {
#ifdef CACHE_WATCH
      elt.watch = c[1].watch;
#endif
    }

    /*
    if(s.state.is_entailed(c[0].atom)) {
      // If we've found something true, don't bother
      // updating the watches: just record the satisfying atom
      // in the head.
      c[1] = elt;
      ch.e0 = c[0].atom;
      ws[jj++] = ch;
      goto next_clause;
    }
    */

    /*
    for(int li = 2; li < c.size(); li++) {
      if(!s.state.is_inconsistent(c[li].atom)) {
        // Literal is not yet false. New watch is found.
        clause_elt new_watch = c[li];
        c[1] = new_watch;
        c[li] = elt;
        // Modifies c[1].watch in place
        ch.e0 = elt.atom;
        // ch.e0 = c[0].atom;
        find_watchlist(s, c[1]).push(ch);
        goto next_clause;
      }
    }
    */
    clause_elt* b(&(c[2]));
    clause_elt* e(c.end());
    for(; b != e; ++b) {
      if(!s.state.is_inconsistent((*b).atom)) {
        clause_elt new_watch = (*b);
        c[1] = new_watch;
        (*b) = elt;
        // Modifies c[1].watch in place
        ch.e0 = elt.atom;
        // ch.e0 = c[0].atom;
        find_watchlist(s, c[1]).push(ch);
        goto next_clause;
      }
    }
    // No watches found; either unit or conflicting.
    c[1] = elt;
    ws[jj++] = ch;
//    assert(c[0].watch);
//    assert(c[1].watch);
    // Save the trail location, so we can tell if it's locked. (NOW DONE IN ENQUEUE)
    // c.extra.depth = s.infer.trail.size();
    if(!enqueue(s, c[0].atom, &c)) {
      for(ii++; ii < ws.size(); ii++)
        ws[jj++] = ws[ii];
      ws.shrink(ii - jj);
      return false;
    }

next_clause:
    continue;
  }
  ws.shrink(ws.size() - jj);
  return true;
}

INLINE_SATTR
bool propagate_ineqs(solver_data& s, pid_t p) {
  pval_t val_p = s.state.p_vals[p];

  for(infer_info::bin_le ineq : s.infer.pred_ineqs[p]) {
    pval_t val_q = val_p - ineq.offset;
    if(s.state.p_vals[ineq.p] >= val_q)
      continue;
    if(!enqueue(s, patom_t { ineq.p, val_q }, reason(p, ineq.offset)))
      return false;
  }
  return true;
}

INLINE_SATTR
bool propagate_pred(solver_data& s, pid_t p) {
  // Process watches
  watch_node* curr = s.infer.pred_watches[p];
  patom_t atom(p, curr->succ_val);

  while(s.state.is_entailed(atom)) {
    assert(curr->succ);
    curr = curr->succ;

    for(patom_t at : curr->bin_ws) {
      if(!enqueue(s, at, ~atom))
        return false;
    }

    if(!update_watchlist(s, ~atom, curr->ws)) {
      return false;
    }
    /*
    for(watch_callback call : curr->callbacks)
      call();
      */
    run_watches(curr->callbacks, s.pred_origin[p]);
    atom.val = curr->succ_val;
  }

  // Propagate binary inequalities
  if(!propagate_ineqs(s, p))
    return false;

  // Trail head of watches 
  if(curr != s.infer.pred_watches[p]) {
    s.persist.pwatch_trail.push({p, s.infer.pred_watches[p]});
    s.infer.pred_watches[p] = curr;
  }
   
  return true;
}


INLINE_SATTR
void wakeup_pred(solver_data& s, pid_t p) {
  s.active_prop = s.pred_origin[p];
  for(watch_callback call : s.pred_callbacks[p]) {
    call();
  }
  s.wake_vals[p] = s.state.p_vals[p];
  s.wake_queued[p] = false;
}

void attach(solver_data* s, patom_t p, const watch_callback& cb) {
  watch_node* watch = s->infer.get_watch(p.pid, p.val);
  watch->callbacks.push(cb);
}

void prop_cleanup(solver_data& s) {
  // Make sure all modified preds are touched
  while(!s.pred_queue.empty()) {
    pid_t pi = s.pred_queue._pop();
    s.pred_queued[pi] = false;
    touch_pred(s, pi);
  }
  for(pid_t pi : s.wake_queue) {
    touch_pred(s, pi);
    s.wake_queued[pi] = false;
  }
  s.wake_queue.clear();

  uint32_t nonempty_queues(s.queue_has_prop);
  while(nonempty_queues) {
    unsigned prio(__builtin_ctz(nonempty_queues));
    nonempty_queues &= nonempty_queues-1;

    auto& Q(s.prop_queue[prio]);
    while(!Q.empty()) {
      propagator* p = Q._pop();
      p->cleanup();
    }
  }
  for(int p = 0; p < PRIO_LEVELS; ++p)
    assert(s.prop_queue[p].empty());
  s.queue_has_prop = 0;

  // s.active_prop = nullptr;
  clear_reset_flags(s);
}

bool propagate(solver_data& s) {
  // Propagate any entailed clauses
  while(!s.pred_queue.empty()) {
prop_restart:
    pid_t pi = s.pred_queue._pop();
    // We rely on wake_queue to
    s.pred_queued[pi] = false;
    if(!s.wake_queued[pi]) {
      s.wake_queue.push(pi);
      s.wake_queued[pi] = true;
    }

    s.active_prop = nullptr;
    if(!propagate_pred(s, pi)) {
      prop_cleanup(s);
#ifdef CHECK_STATE
      check_at_fixpoint(&s);
#endif
      return false;
    }
  }
  
  // Fire any events for the changed predicates
#ifdef PROOF_LOG
  s.log.active_constraint = 0;
#endif
  for(pid_t pi : s.wake_queue) {
    assert(0 <= pi && pi < num_preds(&s));
    touch_pred(s, pi);
    wakeup_pred(s, pi);
  }
  s.wake_queue.clear();

  // Process enqueued propagators
  while(s.queue_has_prop) {
    unsigned prio(__builtin_ctz(s.queue_has_prop));
    auto& Q(s.prop_queue[prio]);
    while(!Q.empty()) {
      propagator* p = Q._pop();
#ifdef PROOF_LOG
      s.log.active_constraint = p->cons_id;
#endif
      s.active_prop = (void*) p;
#ifdef TRACK_EXEC_COUNT
      p->exec_count++;
#endif
      if(!p->propagate(s.infer.confl)) {
#ifdef LOG_PROP
        cerr << "[>Done-]" << endl;
#endif
#ifdef CHECK_STATE
        assert(decision_level(s) == 0 || confl_is_current(&s, s.infer.confl));
#endif

        p->cleanup();
        prop_cleanup(s);
#ifdef CHECK_EXPLNS
        assert(check_confl(&s, p, s.infer.confl));
#endif
        s.active_prop = nullptr;
#ifdef CHECK_STATE
    check_at_fixpoint(&s);
#endif
        return false; 
      }
#ifdef LOG_PROP
        cerr << "[>Done+]" << endl;
#endif
      p->cleanup();

      // If one or more predicates were updated,
      // jump back to 
      if(!s.pred_queue.empty()) {
        s.active_prop = nullptr;
        goto prop_restart;
      }
    }
    s.queue_has_prop &= ~(1<<prio);
  }
  s.active_prop = nullptr;
  /*  
  if(!s.pred_queue.empty())
    goto prop_restart;
    */

  clear_reset_flags(s);
#ifdef CHECK_STATE
  check_at_fixpoint(&s);
#endif
  
#if 0
  for(propagator* p : s.propagators) {
    assert(p->check_sat());
  }
#endif
  return true;
}

//inline
void add_learnt(solver_data* s, vec<clause_elt>& learnt, bool one_watch) {
  // Allocate the clause
  // GEAS_WARN("Collection of learnt clauses not yet implemented.");
#ifdef CHECK_STATE
  for(int ei = 1; ei < learnt.size(); ei++)
    assert(s->state.is_inconsistent(learnt[ei].atom));
#endif

  // Construct the clause
  int jj = 0;
  for(clause_elt e : learnt) {
    // Remove anything dead at l0.
    if(s->state.is_inconsistent_l0(e.atom))
      continue;
    learnt[jj++] = e;
  }
  learnt.shrink(learnt.size()-jj);

  s->stats.num_learnts++;
  s->stats.num_learnt_lits += jj;
  
  // Unit at root level
  if(learnt.size() == 1) {
    enqueue(*s, learnt[0].atom, reason()); 
    return;
  }
  
  // Binary clause; embed the -other- literal
  // in the head;
  /*  */ if(learnt.size() == 2) /* / if(0) */ {
    // Add the two watches
    /*
    clause_head h0(learnt[0].atom);
    clause_head h1(learnt[1].atom);

    find_watchlist(*s, learnt[0]).push(h1);
    find_watchlist(*s, learnt[1]).push(h0); 
    */
    find_bin_watchlist(*s, learnt[0]).push(learnt[1].atom);
    find_bin_watchlist(*s, learnt[1]).push(learnt[0].atom);
    enqueue(*s, learnt[0].atom, learnt[1].atom);
  } else {
    // Normal clause
#ifdef KEEP_GLUE
    bool is_glue = true;
    for(int ii = 1; ii < learnt.size(); ii++)
      if(s->state.is_inconsistent_prev(learnt[ii].atom))
        is_glue = false;
#else
    bool is_glue = false;
#endif

    clause* c(clause_new(learnt));
    c->extra.is_learnt = true;
    c->extra.one_watch = one_watch;
    // c->extra.depth = s->infer.trail.size(); // NOW DONE IN ENQUEUE

    // Assumption:
    // learnt[0] is the asserting literal;
    // learnt[1] is at the current level
    // clause_head h(learnt[2].atom, c);
    clause_head h(learnt.last().atom, c);

    if(!one_watch)
      find_watchlist(*s, (*c)[0]).push(h);
    find_watchlist(*s, (*c)[1]).push(h); 
    enqueue(*s, learnt[0].atom, c);
    if(is_glue)
      s->infer.clauses.push(c);
    else
      s->infer.learnts.push(c);
  }
}

// Remove c from its watch lists.
inline void detach_watch(vec<clause_head>& ws, clause* c) {
  for(clause_head& w : ws) {
    if(w.c == c) {
      w = ws.last();
      ws.pop();
      return;
    }
  }
  GEAS_ERROR;
}

inline void replace_watch(vec<clause_head>& ws, clause* c, clause_head h) {
  for(clause_head& w : ws) {
    if(w.c == c) {
      w = h;
      return;
    }
  }
}

inline void detach_clause(solver_data& s, clause* c) {
  // We care about the watches for 
  // fprintf(stderr, "%p\n", c);
  if(!c->extra.one_watch)
    detach_watch(lookup_watchlist(s, (*c)[0]), c);
  detach_watch(lookup_watchlist(s, (*c)[1]), c);
}

inline clause** simplify_clause(solver_data& s, clause* c, clause** dest) {
  /*
  clause_elt* ej = c->begin();
  for(clause_elt e : *c) {
    */
  // If a watch is true, delete it.
  if(s.state.is_entailed_l0((*c)[0].atom)
     || s.state.is_entailed_l0((*c)[1].atom)) {
    detach_clause(s, c);
    free(c);
    return dest;
  }
  
  // Simplify the other elements
  clause_elt* ej = c->begin()+2;
  for(int ei = 2; ei < c->size(); ei++) {
    clause_elt e = (*c)[ei]; 
    if(s.state.is_entailed_l0(e.atom)) {
      // Clause is satisfied at the root; remove it.
      detach_clause(s, c);
      free(c); 
      return dest;
    }
    if(!s.state.is_inconsistent_l0(e.atom)) {
      // Literal may become true; keep it.
      *ej = e; ++ej;
    }
  }
  c->sz = ej - c->begin();
  assert(c->sz >= 2);

  if(c->sz == 2)  {
    // c has become a binary clause.
    // Inline the clause body, and free the clause.
    // GKG: Should check if this is locked.
    // >> Should be safe so long as we're at level 0.
    // FIXME: There is a risk when it comes to one-literal watching:
    // there may only be one survivor in the clause, so if we were
    // two-watching, it would already be asserted.
    // As it is, one of our watch-lists will already be dead.
    detach_clause(s, c);
    /*
    if(!c->extra.one_watch)
      replace_watch(find_watchlist(s, (*c)[0]), c, (*c)[1].atom);
    replace_watch(find_watchlist(s, (*c)[1]), c, (*c)[0].atom);
    */
    find_bin_watchlist(s, (*c)[0]).push((*c)[1].atom);
    find_bin_watchlist(s, (*c)[1]).push((*c)[0].atom);
    free(c);
    return dest;
  }

  *dest = c; ++dest;
  return dest;
}

// Precondition: propagate should have been run to fixpoint,
// and we're at decision level 0.
inline void simplify_at_root(solver_data& s) {
  // Update predicate values, simplify clauses
  // and clear trails.
  // for(int pi = 0; pi < s.pred_callbacks.size(); pi++) {
  for(int pi : s.persist.touched_preds) {
    s.state.p_last[pi] = s.state.p_vals[pi];
    s.state.p_root[pi] = s.state.p_vals[pi];
    s.wake_vals[pi] = s.state.p_vals[pi];
  }

#if 1
  // Watches may be invalidated when a clause is
  // deleted because it is satisfied at the root.
  // This is dealt with in simplify_clause.
  clause** cj = s.infer.clauses.begin();
  // for(clause* c : s.infer.clauses) {
  for(int ci = 0; ci < s.infer.clauses.size(); ci++) {
    clause* c(s.infer.clauses[ci]);
    cj = simplify_clause(s, c, cj); 
  }
  s.infer.clauses.shrink_(s.infer.clauses.end() - cj);

  clause** lj = s.infer.learnts.begin();
  for(clause* c : s.infer.learnts) {
    lj = simplify_clause(s, c, lj);
  }
  s.infer.learnts.shrink_(s.infer.learnts.end() - lj);
#endif

#if 1
  for(int pi : s.persist.touched_preds) {
    // Do garbage collection on the watch_node*-s.
    pval_t head_val = s.infer.pred_watch_heads[pi].val;
    watch_node* head = s.infer.pred_watch_heads[pi].ptr;
    watch_node* dest = s.infer.pred_watches[pi];

    while(head != dest) {
      // assert(head->ws.size() == 0);
#if 0
      // FIXME: This is dangerous in combination with
      // one-watch. See note in simplify_clause.
      s.infer.watch_maps[pi].rem(head_val);
      watch_node* w = head;
      head_val = head->succ_val;
      head = head->succ;
      delete w;
#else
      head_val = head->succ_val;
      head = head->succ;
#endif
    }

    s.infer.pred_watch_heads[pi].val = head_val;
    s.infer.pred_watch_heads[pi].ptr = head;
    // Now that entailed watches are deleted, we're committed
    // to simplifying all the clauses.
    // TODO: Also collect inactive watch-nodes.
  }
#endif

#if 0
    for(int pi : irange(s.infer.pred_watches.size())) {
      watch_node* w = s.infer.pred_watches[pi];
      watch_node* su = w->succ;
      pval_t succ_val = w->succ_val;
      while(su) {
        if(su->ws.size() == 0 && su->callbacks.size() == 0) {
          s.infer.watch_maps[pi].rem(succ_val);
          watch_node* r(su);
          succ_val = r->succ_val;
          su = r->succ;
          delete r;
        } else {
          w->succ_val = succ_val;
          w->succ = su;
          w = su;
          succ_val = su->succ_val;
          su = su->succ;
        }
      }
      w->succ = nullptr;
      w->succ_val = pval_err;
    }
#endif


#ifdef LOG_RESTART
  int count = 0;
  int stale = 0;
  for(watch_node* w : s.infer.pred_watches) {
    while(w->succ) {
      w = w->succ;
      ++count;
      if(w->ws.size() == 0 && w->callbacks.size() == 0)
        ++stale;
    }
  }
  fprintf(stderr, "%% %d watch nodes, %d stale\n", count, stale);
  fprintf(stderr, "%% %d propagations, %d clauses, %d learnts\n", num_props,
    s.infer.clauses.size(), s.infer.learnts.size());
  fprintf(stderr, "%% %lf possible values\n", domains_total);
#endif
  

  for(propagator* p : s.propagators)
    p->root_simplify();
  
  // Now reset all persistence stuff. 
   s.infer.root_simplify();
   s.persist.root_simplify();

  return;
}

// Retrieve a model
// precondition: last call to solver::solve returned SAT
// actually, we should just save the last incumbent.
void save_model(solver_data* data) {
  data->incumbent.vals.clear(); 
  vec<pval_t>& vals(data->state.p_vals);
  for(pid_t pi : num_range(0, vals.size()/2))
    data->incumbent.vals.push(vals[2*pi]);
}
  
model solver::get_model(void) {
  return data->incumbent;
}

void bump_touched(solver_data& s,
  double mult, double alpha, int confl_num, int touched_start) {
  for(int ti = touched_start; ti < s.persist.touched_preds.size(); ti++) {
    // pid_t p = s.persist.touched_preds[ti];
    pid_t p = s.persist.touched_preds[ti]>>1;
    double reward = mult * (confl_num - s.confl.pred_saved[p].last_seen + 1);
    double& act = s.infer.pred_act[p];
    act = (1 - alpha)*act + alpha*reward;
    if(s.pred_heap.inHeap(p))
      s.pred_heap.decrease(p);
  }
}

void save_touched(solver_data& s, int touched_start) {
  if(s.stats.solutions) {
    for(int ti = touched_start; ti < s.persist.touched_preds.size(); ti++) {
      pid_t p = s.persist.touched_preds[ti];
      if(!s.polarity[p>>1].has_preference)
        s.polarity[p>>1].branch = 1^(p&1);
    }
    return;
  }

  for(int ti = touched_start; ti < s.persist.touched_preds.size(); ti++) {
    pid_t p = s.persist.touched_preds[ti];
#if 0
    pval_t k = (p&1) ? pval_inv(s.state.p_vals[p]) : s.state.p_vals[p];
    s.confl.pred_saved[p>>1].val += 0.01 * (s.confl.pred_saved[p>>1].val - k);
#else
    if(p&1) {
      s.confl.pred_saved[p>>1].val = pval_inv(s.state.p_vals[p]);
    } else {
      s.confl.pred_saved[p>>1].val = s.state.p_vals[p];
    }
    s.polarity[p>>1].branch = 1^(p&1);
    // s.confl.pred_saved[p>>1].val = p&1;
#endif
  }
}

void solver::abort(void) {
  data->abort_solve = 1;
}

bool solver::is_aborted(void) const { return global_abort || data->abort_solve; }

// Solving
solver::result solver::solve(limits l) {
  // Top-level failure
  sdata& s(*data);
  s.abort_solve = 0;
  int confl_num = 0;
  s.infer.confl.clear();

  if(!s.solver_is_consistent)
    return UNSAT;

  /* Establish a handler for SIGINT and SIGTERM signals. */
  set_handlers();

#ifdef REPORT_INTERNAL_STATS
  stat_reporter rep(data);
#endif
//  int max_conflicts = 200000;
  int max_conflicts = l.conflicts;
  double max_time = INFINITY;
  double start_time = getTime();
   
  // Activity stuff
  // FIXME: add persistence to confl_num, so we don't need
  // to reset this.
  double alpha = 0.4;
//  for(double& act : s.infer.pred_act)
//    act = 0;

  int restart_lim = s.opts.restart_limit;
#ifdef RESTART_LUBY
  unsigned int luby_m = 1;
  unsigned int luby_r = 0;
#endif

  // FIXME: On successive runs, this may be smaller than
  // the existing database
  int gc_lim = s.learnt_dbmax;

  int next_restart = restart_lim ? restart_lim : INT_MAX;
  int next_gc = max(1, gc_lim - s.infer.learnts.size());
  // int next_gc = gc_lim - s.infer.learnts.size();
  int budget = max_conflicts;

  int next_pause = min(next_restart, next_gc);
  if(budget)
    next_pause = min(next_pause, budget);

  if(l.time > 0) {
    max_time = getTime() + l.time;
    next_pause = min(next_pause, 100);
  }
#ifdef LOG_ALL
      log_state(s.state);
#endif

  process_initializers(s);

  while(true) {
    // Signal handler
    if(global_abort || s.abort_solve) {
      // fprintf(stderr, "%% Aborting solve.\n");
      global_abort = 0;
      s.abort_solve = 0;

      clear_handlers();
      prop_cleanup(s);
      s.stats.conflicts += confl_num;
      s.stats.time += getTime() - start_time;
      return UNKNOWN;
    }

    int touched_start = s.persist.touched_preds.size();
    if(!propagate(s)) {
      // bump_touched(s, 1.0, alpha, /* s.stats.conflicts + */ confl_num, touched_start);
      bump_touched(s, 1.0, alpha, s.stats.conflicts + confl_num, touched_start);
      save_touched(s, touched_start);
      if(alpha > 0.06)
        alpha = alpha - 1e-6;

#ifdef CHECK_STATE
      int pi = decision_level(s) > 0 ? s.infer.trail_lim.last() : 0;
      for(; pi < s.infer.trail.size(); pi++)
        assert(s.persist.pred_touched[s.infer.trail[pi].pid]);
#endif

      ++confl_num;
#ifdef LOG_ALL
      cout << "Conflict [" << confl_num << "|" << s.stats.conflicts << "]: " << s.infer.confl << endl;
#endif
      if(decision_level(s) == 0) {
        s.stats.conflicts += confl_num;
        s.stats.time += getTime() - start_time;
        s.infer.confl.clear();
        s.last_confl = { C_Infer, 0 };
        clear_handlers();
        s.solver_is_consistent = false;
        return UNSAT;
      }
        
      // Conflict
      int bt_level = compute_learnt(&s, s.infer.confl);
#ifdef LOG_ALL
      cout << "Learnt: " << s.infer.confl << endl;
      cout << "*" << bt_level << ">" << endl;
#endif
#ifdef CHECK_STATE
      for(int ei = 1; ei < s.infer.confl.size(); ei++)
        assert(s.state.is_inconsistent(s.infer.confl[ei].atom));
#endif
      if(bt_level < s.infer.trail_lim.size())
        bt_to_level(&s, bt_level);
      process_initializers(s);
#ifdef CHECK_STATE
      assert(s.infer.confl[0].atom.ub(s.state.p_vals));
      for(int ei = 1; ei < s.infer.confl.size(); ei++)
        assert(s.state.is_inconsistent(s.infer.confl[ei].atom));
#endif
#ifdef CHECK_STATE
      for(pid_t p : s.persist.touched_preds)
        assert(s.wake_vals[p] == s.state.p_vals[p]);
#endif

#ifdef LOG_ALL
      log_state(s.state);
#endif

#ifdef CHECK_STATE
      check_pvals(&s);

      if(bt_level == 0) {
        for(int pi = 0; pi < s.state.p_vals.size(); pi++)
          assert(s.state.p_vals[pi] == s.state.p_root[pi]);
      }
#endif

      // add_learnt(&s, s.infer.confl);
      add_learnt(&s, s.infer.confl, s.opts.one_watch);
      s.infer.confl.clear();

      if(confl_num == next_pause) {
        s.stats.conflicts += confl_num;
        next_restart -= confl_num;
        next_gc -= confl_num;

        if(budget) {
          // cout << budget << ", " << confl_num << endl;
          budget -= confl_num;
          if(!budget) {
            clear_handlers();
            s.stats.time += getTime() - start_time;
            return UNKNOWN;
          }
        }

        confl_num = 0;

        if(next_restart == 0) {
#ifdef LOG_RESTART
          cout << "%%%% [| Restarting |]" << endl;
#endif
          s.stats.restarts++;
  
#ifdef RESTART_LUBY
          if(luby_r & luby_m) {
            luby_r ^= luby_m;
            luby_m <<= 1;
          } else {
            luby_r |= luby_m;
          }
          next_restart = restart_lim * luby_m;
#else
          next_restart = restart_lim = restart_lim * s.opts.restart_growthrate;
#endif
          if(decision_level(s) > 0) {
            prop_cleanup(s);
            bt_to_level(&s, 0);
            process_initializers(s);
          }
          run_callbacks(s.on_restart);
#ifdef LOG_ALL
      log_state(s.state);
#endif
#ifdef CHECK_STATE
          for(int pi = 0; pi < s.state.p_vals.size(); pi++)
            assert(s.state.p_vals[pi] == s.state.p_root[pi]);
#endif
        }
        if(next_gc == 0) {
#ifdef LOG_GC
          cout << "[| GC : " << s.infer.learnts.size() << "|]";
#endif
          if(s.infer.learnts.size() >= gc_lim) {
            reduce_db(&s);
            gc_lim = gc_lim * s.opts.learnt_growthrate;
          }
          next_gc = gc_lim - s.infer.learnts.size();
#ifdef LOG_GC
          cout << " ~~> " << s.infer.learnts.size()
            << " {" << s.infer.trail.size() << " trail}" << endl;
#endif
        }

        next_pause = min(next_restart, next_gc);
        if(budget)
          next_pause = min(next_pause, budget);
        if(isfinite(max_time)) {
          if(getTime() > max_time) {
            clear_handlers();
            s.stats.time += getTime() - start_time;
            return UNKNOWN;
          }
          // FIXME: Do something adaptive here.
          next_pause = min(next_pause, 100);
        }
      }
      continue;
    }
#ifdef CHECK_STATE
    for(pid_t p : s.persist.touched_preds)
      assert(s.wake_vals[p] == s.state.p_vals[p]);
#endif

    // bump_touched(s, 0.9, alpha, /* s.stats.conflicts + */ confl_num, touched_start);
    bump_touched(s, 0.9, alpha, s.stats.conflicts + confl_num, touched_start);

#ifdef CHECK_STATE
    int ti = decision_level(s) > 0 ? s.infer.trail_lim.last() : 0;
    for(; ti < s.infer.trail.size(); ti++)
      assert(s.persist.pred_touched[s.infer.trail[ti].pid]);

    /*
    // This _can_ happen legitimately - when we add a new learnt c,
    // c[1] will already be false (so the watch node will be entailed.
    // But it shouldn't inherently be a problem.

    for(int pi = 0; pi < s.infer.pred_watches.size(); pi++) {
      assert(s.infer.pred_watches[pi]->succ_val > s.state.p_vals[pi]);
    }
    */
#endif

    if(decision_level(s) == 0)
      simplify_at_root(s);

    patom_t dec = at_Undef;
    
    int assump_idx = s.assump_end;
    if(assump_idx < s.assumptions.size()) {
      for(; assump_idx < s.assumptions.size(); ++assump_idx) {
        s.assump_level[assump_idx] = decision_level(s);
        patom_t at(s.assumptions[assump_idx]);
        if(is_entailed(s, at))
          continue;

        if(is_inconsistent(s, at)) {
          s.last_confl = { C_Assump, assump_idx };
          s.stats.conflicts += confl_num;
          s.stats.time += getTime() - start_time;
          clear_handlers();
          return UNSAT; 
        }

        // Found an atom to branch on
        dec = at;
        // ++idx;
        break;
      }
      // trail_change(s.persist, s.assump_end, idx);
    }
    
    if(dec == at_Undef)
      dec = branch(&s);

    if(dec == at_Undef) {
      save_model(data);
      s.stats.conflicts += confl_num;
      s.stats.solutions++;
      s.stats.time += getTime() - start_time;
      clear_handlers();

      run_callbacks(s.on_solution);

      // Check that assumptions are, indeed,
      // satisfied.
#ifdef CHECK_STATE
      for(patom_t a : s.assumptions) {
        assert(a.lb(s.state.p_vals));
      }

      for(propagator* p : s.propagators) {
        assert(p->check_sat(s.state.p_vals));
      }
#endif
#ifdef LOG_ALL
      for(patom_t a : s.assumptions) {
        cerr << "[" << a << "]" << endl;
      }
#endif
      return SAT;
    }

    assert(!s.state.is_entailed(dec));
    assert(!s.state.is_inconsistent(dec));
#ifdef LOG_ALL
    cout << "?" << s.infer.trail_lim.size() << "> " << dec << endl;
#endif

    push_level(&s);

    if(assump_idx > s.assump_end)
      trail_change(s.persist, s.assump_end, assump_idx);

    enqueue(s, dec, reason());

    run_callbacks(s.on_branch);
  }

  // Unreachable
  GEAS_ERROR;
  clear_handlers();
  return SAT;
}

 
// For incremental solving; any constraints
// added after a push are paired with an activation
// literal.
void solver::level_push(void) {
  GEAS_NOT_YET;   
}

// Drop any constraints added at the current
// context. 
void solver::level_pop(void) {
  GEAS_NOT_YET; 
}

void solver::get_conflict(vec<patom_t>& confl) {
  retrieve_assumption_nogood(data, confl);
}

// For subsumption detection
struct {
  bool operator()(const clause_elt& x, const clause_elt& y) const {
    if(x.atom.pid == y.atom.pid)
      return x.atom.val < y.atom.val; 
    return x.atom.pid < y.atom.pid;
  }
} cmp_clause_elt;

// Add a clause at the root level.
bool add_clause(solver_data& s, vec<clause_elt>& elts) {
  int jj = 0;
  for(clause_elt e : elts) {
    if(s.state.is_entailed(e.atom))
      return true;
    if(s.state.is_inconsistent(e.atom))
      continue;
    elts[jj++] = e;
  }
  elts.shrink(elts.size()-jj);
  
  // False at root level
  if(elts.size() == 0) {
    s.solver_is_consistent = 0;
    return false;
  }

  // Now check for subsumption
  sort(elts.begin(), elts.end(), cmp_clause_elt);
  jj = 1;
  for(int ii = 1; ii < elts.size(); ++ii) {
    if(elts[ii-1].atom.pid != elts[ii].atom.pid) {
      elts[jj++] = elts[ii];
    }
  }
  elts.shrink(elts.size()-jj);

  // Unit at root level
  if(elts.size() == 1)
    return enqueue(s, elts[0].atom, reason()); 
  
  // Binary clause; embed the -other- literal
  // in the head;
  if(elts.size() == 2) {
    /*
    clause_head h0(elts[0].atom);
    clause_head h1(elts[1].atom);

    find_watchlist(s, elts[0]).push(h1);
    find_watchlist(s, elts[1]).push(h0); 
    */
    find_bin_watchlist(s, elts[0]).push(elts[1].atom);
    find_bin_watchlist(s, elts[1]).push(elts[0].atom);
  } else {
    // Normal clause
    clause* c(clause_new(elts));
    // Any two watches should be fine
    clause_head h(elts.last().atom, c);

    find_watchlist(s, (*c)[0]).push(h);
    find_watchlist(s, (*c)[1]).push(h); 
    s.infer.clauses.push(c);
  }
  return true;
}

// Add a clause, but not necessarily at the root level.
bool add_clause_(solver_data& s, vec<clause_elt>& elts) {
  int jj = 0;
  int kk = 0;
  for(clause_elt e : elts) {
    if(s.state.is_entailed_l0(e.atom))
      return true;
    if(s.state.is_inconsistent_l0(e.atom))
      continue;
    // if(s.state.is_inconsistent_prev(e.atom)) {
    if(s.state.is_inconsistent(e.atom)) {
      elts[jj++] = e;
    } else {
      elts[jj++] = elts[kk];
      elts[kk++] = e;
    }
  }
  elts.shrink(elts.size()-jj);
  
  // False at root level
  if(elts.size() == 0)
    return false;
  // Unit at root level
  /*
  if(elts.size() == 1)
    return enqueue(s, elts[0].atom, reason()); 
    */
  if(elts.size() == 1)
    return true;
  // Binary clause; embed the -other- literal
  // in the head;
  if(elts.size() == 2) {
    /*
    clause_head h0(elts[0].atom);
    clause_head h1(elts[1].atom);

    find_watchlist(s, elts[0]).push(h1);
    find_watchlist(s, elts[1]).push(h0); 
    */
    find_bin_watchlist(s, elts[0]).push(elts[1].atom);
    find_bin_watchlist(s, elts[1]).push(elts[0].atom);
    return true;
    /*
    if(s.state.is_inconsistent(elts[1].atom))
      return enqueue(s, elts[0].atom, elts[1].atom);
      */
  } else {
    // Normal clause
    clause* c(clause_new(elts));
    clause_head h(elts.last().atom, c);

    find_watchlist(s, (*c)[0]).push(h);
    find_watchlist(s, (*c)[1]).push(h); 
    /*
    if(s.state.is_inconsistent(elts[1].atom))
      return enqueue(s, elts[0].atom, c);
      */
    s.infer.clauses.push(c);
    return true;
  }
  return true;
}

}
