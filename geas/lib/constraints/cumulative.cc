#include <climits>
#include <cstring>
#include <algorithm>
#include <geas/solver/solver_data.h>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/constraints/builtins.h>

#include <geas/mtl/bool-set.h>
#include <geas/mtl/p-sparse-set.h>
#include <geas/utils/ordered-perm.h>
// #define LOG_PROFILE
#define LOG_START_AT 0

namespace geas {

// Totally non-incremental time-table propagator.
// ============================================

typedef unsigned int task_id;

enum evt_kind { ET = 0, ST = 1};
/*
struct pevt {
  pevt_kind k;
  task_id task;
  int time;
  int cap;
};

*/

// V is the type of resource consumption.
template <class V>
class cumul {
public:
  class cumul_val : public propagator, public prop_inst<cumul_val> {
    typedef prop_inst<cumul_val> I;
    typedef cumul_val P;

    enum ProfileState { P_Invalid = 0, P_Valid = 1, P_Saved = 2 };

    // Typedefs
    typedef unsigned int task_id;
    typedef trailed<V> TrV;
    struct task_info {
      intvar s;
      int d;
      V r;
    };

    struct evt_info {
      evt_kind kind;  
      task_id task;
      int t;
      V level;
    };

    struct ex_info {
      task_id t;
      int s;
      int e;
    };

    struct {
      bool operator()(const evt_info& x, const evt_info& y) const {
        if(x.t == y.t) {
          // Process ends before starts.
          return x.kind < y.kind;
        }
        return x.t < y.t;
      }
    } pevt_cmp;

    int usage_at(int time, const ctx_t& ctx) const {
      V total(0);
      for(const task_info& t : tasks) {
        if(t.s.ub(ctx) <= time && time < t.s.lb(ctx) + t.d)
          total += t.r;
      }
      return total;
    }
    bool check_sat(ctx_t& ctx) {
      for(const task_info& t : tasks) {
        for(int ti = t.s.lb(ctx) + t.d - 1; ti <= t.s.ub(ctx); ++ti) {
          if(usage_at(t.s.ub(ctx), ctx) <= cap - t.r)
            goto task_placed;
        }
        return false;
      task_placed:
        continue;
      }
      return true;
    }
    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

    // Parameters
    vec<task_info> tasks; // We order tasks by decreasing r.
    V cap; // Maximum resource capacity

    // Persistent state
    Tint active_end;

    p_sparseset profile_tasks;
    p_sparseset active_tasks;

    vec<ex_info> exs;
    char exs_saved;

    // Transient state.
    vec<evt_info> profile;
    boolset lb_change;
    boolset ub_change;
    char profile_state;

    // Helper functions
    inline int est(int xi) const { return lb(tasks[xi].s); }
    inline int eet(int xi) const { return lb(tasks[xi].s) + tasks[xi].d; }
    inline int lst(int xi) const { return ub(tasks[xi].s); }
    inline int let(int xi) const { return ub(tasks[xi].s) + tasks[xi].d; }

    inline V mreq(int xi) const { return tasks[xi].r; }
    inline int dur(int xi) const { return tasks[xi].d; }

    int make_ex(task_id t, int s, int e) {
      this->template save(exs._size(), exs_saved);
      int id = exs.size();
      exs.push(ex_info { t, s, e });
      return id;
    }

    watch_result wake_lb(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_state &= ~(P_Valid);
        queue_prop();
      } else {
        if(lst(ti) < eet(ti)) {
          trail_push(s->persist, profile_tasks.sz);
          profile_tasks.insert(ti);
          profile_state &= ~(P_Valid);
          queue_prop();
        } else if(active_tasks.elem(ti)) {
          lb_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    watch_result wake_ub(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_state &= ~(P_Valid);
        queue_prop();
      } else {
        if(lst(ti) < eet(ti)) {
          trail_push(s->persist, profile_tasks.sz);
          profile_tasks.insert(ti);
          profile_state &= ~(P_Valid);
          queue_prop();
        } else if(active_tasks.elem(ti)) {
          ub_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    void log_ptasks(void) {
      std::cerr << "{";
      for(task_id ti : profile_tasks) {
        std::cerr << ti << ":[" << lst(ti) << "," << eet(ti) << ")|"
          << mreq(ti) << " ";
      }
      std::cerr << "}" << std::endl;
    }

    void log_profile(void) {
      for(evt_info e : profile) {
        std::cerr << e.t << ":" << e.task << ":" << (e.kind == ST ? "+" : "-") << e.level << " ";
      }
      std::cerr << std::endl;
    }

    bool rebuild_profile(vec<clause_elt>& confl) {
#ifdef LOG_PROFILE
      if(s->stats.conflicts > LOG_START_AT) {
      std::cout << "Building profile [" << prop_id << "]:" << std::endl << "-------------------" << std::endl;
      log_ptasks();
      }
#endif

      profile.clear();
      // profile.push(evt_info { ET, INT_MAX, INT_MIN, 0 });
      profile.push(evt_info { ST, INT_MAX, INT_MIN, 0 });
      for(task_id ti : profile_tasks) {
        profile.push(evt_info { ST, ti, lst(ti), mreq(ti) });
        profile.push(evt_info { ET, ti, eet(ti), mreq(ti) });
      }
      std::sort(profile.begin()+1, profile.end(), pevt_cmp);
      profile.push(evt_info { ET, INT_MAX, INT_MAX, 0});

      // Now replace the deltas with actual values

#ifdef LOG_PROFILE
      if(s->stats.conflicts > LOG_START_AT) {
      log_profile();
      }
#endif

      V cumul(0);
      V p_max(0);
      for(evt_info& e : profile) {
        if(e.kind == ST) {
          cumul += e.level;
          if(cumul > p_max) {
            if(cumul > cap) {
              explain_overload(e.t, confl);
              return false;
            }
            p_max = cumul;
          }
        } else {
          cumul -= e.level;
        }
        e.level = cumul;
      }

#ifdef LOG_PROFILE
      if(s->stats.conflicts > LOG_START_AT) {
      log_profile();
      std::cerr << std::endl;
      }
#endif

      // Activate any remaining tasks which might
      // be shifted.
      V req_max(cap - p_max);
      int ti = active_end;
      if(ti < tasks.size() && mreq(ti) > req_max) {
        trail_push(s->persist, active_tasks.sz);
        active_tasks.insert(ti);
        for(++ti; ti < tasks.size(); ++ti) {
          if(mreq(ti) <= req_max)
            break;
          assert(!active_tasks.elem(ti));
          active_tasks.insert(ti);
        }
        set(active_end, ti);
      }
      return true;
    }

    bool sweep_fwd(task_id ti) {
      // Find the starting interval
      const task_info& t(tasks[ti]);

      evt_info* s = std::upper_bound(profile.begin(), profile.end(),
        est(ti), [](const int& t, const evt_info& e) { return t <= e.t - (e.kind == ET) ; });
      if(s == profile.end())
        return true;
      // Task stats in the previous interval   
      V lev_max = cap - mreq(ti);

      int end_time = est(ti) + t.d;
      if(s[-1].task == ti)
        return true;
      int ex_time = s[-1].t;
      V seg_level = s[-1].level;

      while(ex_time < end_time) {
        if(seg_level > lev_max) {
          // Shift start and reset.
          if(!set_lb(t.s, s->t, this->template expl<&P::ex_est>(make_ex(ti, ex_time, s->t), expl_thunk::Ex_BTPRED)))
            return false;
          end_time = s->t + t.d;
        }
        // The profile's going to be updated anyway.
        if(s->task == ti)
          return true;
        ex_time = s->t;
        seg_level = s->level;
        ++s;
      }
      return true;
    }

    bool sweep_bwd(task_id ti) {
#if 0
      return true;
#endif
      // Find the starting interval
      const task_info& t(tasks[ti]);

      // evt_info* s = profile.begin();
      // while(s->t - (s->kind == ET) < let(ti)) ++s;
      evt_info* s = std::upper_bound(profile.begin(), profile.end(),
        let(ti), [](const int& t, const evt_info& e) { return t < e.t + (e.kind == ST) ; });
      if(s == profile.begin())
        return true;
      // Task stats in the previous interval   
      V lev_max = cap - mreq(ti);

      int start_time = lst(ti);
      int ex_time = s->t;
      if(s->task == ti)
        return true;

      --s;
      do {
        assert(ex_time > start_time);
        if(s->task == ti)
          return true;
        if(s->level > lev_max) {
          // Shift start and reset.
          if(!set_ub(t.s, s->t - t.d, this->template expl<&P::ex_let>(make_ex(ti, s->t, ex_time), expl_thunk::Ex_BTPRED)))
            return false;
          start_time = s->t - t.d;
        }
        // The profile's going to be updated anyway.
        ex_time = s->t;
        --s;
      } while(ex_time > start_time);
      return true;
    }

    inline void EX_PUSH(vec<clause_elt>& expl, patom_t at) {
      assert(!ub(at));
      expl.push(at);
    }

    void ex_est(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);
      // int t_est(std::max(t.s.lb_of_pval(p), e.ex_time+1));

      // Assumption: we're doing stepwise-propagation.
      // So at this point, lb(t.s) < est, and every task
      // active at (est-1) was active from lb(t.s) + dur - 1.
      
      // So, we collect a sufficient set of tasks, active at
      // (est-1).
      V e_req = (cap - t.r);
      vec<task_id> etasks;
      for(task_id p : profile_tasks) {
        if(lst(p) <= e.s && e.e <= eet(p)) {
          // if(p == ti)
          //   continue;
          assert(p != ti);
          // assert(lst(p) >= lb(t.s));

          etasks.push(p);
          if(e_req < mreq(p)) {
            // Found a cover. Minimize, and find a relaxed
            // lb for t.
            V slack = mreq(p) - e_req;
            
            int jj = 0;
            for(int ii = 0; ii < etasks.size(); ++ii) {
              if(mreq(p) < slack) {
                slack -= mreq(p);
                continue;
              }
              etasks[jj++] = etasks[ii];
            }
            etasks.shrink_(etasks.size() - jj);
            // Now construct the actual explanation
            // Either t is entirely before earliest...
            EX_PUSH(expl, t.s <= e.s - t.d);
            // ...or some member of etasks doesn't cover.
            for(task_id p : etasks) {
              EX_PUSH(expl, tasks[p].s > e.s);
              EX_PUSH(expl, tasks[p].s < e.e - tasks[p].d);
            }
            return;
          }
          e_req -= mreq(p);
        }
      }
      // Should be unreachable
      GEAS_ERROR;
    }

    void ex_let(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);
      // int t_let(std::min(t.s.ub_of_pval(p) + t.d, e.ex_time));

      V e_req = (cap - t.r);
      vec<task_id> etasks;
      for(task_id p : profile_tasks) {
        // if(lst(p) < e.ex_time && e.ex_time <= eet(p)) {
        if(lst(p) <= e.s && e.e <= eet(p)) {
          // assert(p != ti);
          if(p == ti)
            continue;
          // assert(lst(p) >= lb(t.s));

          etasks.push(p);
          if(e_req < mreq(p)) {
            // Found a cover. Minimize, and find a relaxed
            // lb for t.
            V slack = mreq(p) - e_req;
            
            int jj = 0;
            for(int ii = 0; ii < etasks.size(); ++ii) {
              if(mreq(p) < slack) {
                slack -= mreq(p);
                continue;
              }
              etasks[jj++] = etasks[ii];
            }
            etasks.shrink_(etasks.size() - jj);
            // Now construct the actual explanation
#if 1
            // Either t is pushed after e.ex_time...
            // EX_PUSH(expl, t.s >= e.ex_time);
            EX_PUSH(expl, t.s >= e.e);
            // ...or some member of etasks doesn't cover.
            for(task_id p : etasks) {
              // EX_PUSH(expl, tasks[p].s > t_let);
              // EX_PUSH(expl, tasks[p].s < e.ex_time - tasks[p].d);
              EX_PUSH(expl, tasks[p].s > e.s);
              EX_PUSH(expl, tasks[p].s < e.e - tasks[p].d);
            }
#else
            // Semi-naive explanation
            expl.push(t.s > ub(t.s));
            for(task_id p : etasks) {
              expl.push(tasks[p].s < lb(tasks[p].s));
              expl.push(tasks[p].s > ub(tasks[p].s));
            }
#endif
            return;
          }
          e_req -= mreq(p);
        }
      }
      // Should be unreachable
      GEAS_ERROR;
    }

    void explain_overload(int t, vec<clause_elt>& confl) {
      // Usual trick: collect a sufficient set of tasks, then
      // discard until we have a minimal set.
      vec<task_id> e_tasks;
      V to_cover(cap);
      for(task_id p : profile_tasks) {
        if(lst(p) <= t && t < eet(p)) {
          e_tasks.push(p);
          if(to_cover < mreq(p)) {
            // Found a sufficient cover.
            V slack(mreq(p) - to_cover);
            for(task_id q : e_tasks) {
              // Can be omitted; we have sufficient
              // slack later on.
              if(mreq(q) < slack) {
                slack -= mreq(q);
                continue;
              }
              EX_PUSH(confl, tasks[q].s <= t - tasks[q].d);
              EX_PUSH(confl, tasks[q].s > t);
            }
            return;
          }
          to_cover -= mreq(p);
        }
      }
      GEAS_ERROR;
    }

  public:
    cumul_val(solver_data* s, vec<intvar>& starts, vec<int>& dur, vec<V>& res, V _cap)
      : propagator(s), cap(_cap)
      , active_end(0)
      , profile_tasks(starts.size())
      , active_tasks(0)
      , exs_saved(false)
      , profile()
      , lb_change(starts.size())
      , ub_change(starts.size())
      , profile_state(P_Invalid) {
      for(int xi : irange(starts.size())) {
        // If a task has zero duration or resource consumption, skip it.
        if(!dur[xi] || !res[xi])
          continue;
        if(res[xi] > cap)
          throw RootFail();
        task_info t(task_info { starts[xi], dur[xi], res[xi] });
        tasks.push(t);
      }
      active_tasks.growTo_strict(tasks.size());
      std::sort(tasks.begin(), tasks.end(), [](const task_info& x, const task_info& y) { return x.r > y.r; });
      for(int xi: irange(tasks.size())) {
        task_info& t(tasks[xi]);
        t.s.attach(E_LB, this->template watch<&P::wake_lb>(xi));
        t.s.attach(E_UB, this->template watch<&P::wake_ub>(xi));
        // tasks.push(t);
        if(lst(xi) < eet(xi)) {
          profile_tasks.insert(xi);
        }
      }
    }

    bool propagate(vec<clause_elt>& confl) {
      // fprintf(stderr, "Active: %d of %d\n", active_tasks.size(), tasks.size());
      if(!(profile_state & P_Valid)) {
        if(!(profile_state & P_Saved))
          s->persist.bt_flags.push(&profile_state);
        if(!rebuild_profile(confl))
          return false;
        profile_state = (P_Saved & P_Valid);
#if 1
        for(task_id t : active_tasks) {
          if(is_fixed(tasks[t].s)) {
            assert(profile_tasks.elem(t));
            continue;
          }
          if(!sweep_fwd(t))
            return false;
          if(!sweep_bwd(t))
            return false;   
        }
#endif
      } else {
        // If the profile hasn't changed, only sweep
        // variables with updated bounds.
#if 1
        for(task_id t : lb_change) {
          if(is_fixed(tasks[t].s))
            continue;
          if(!sweep_fwd(t))
            return false;
        }
        for(task_id t : ub_change) {
          if(is_fixed(tasks[t].s))
            continue;
          if(!sweep_bwd(t))
            return false;
        }
#endif
      }
      return true;
    }

    void cleanup(void) {
      lb_change.clear();
      ub_change.clear();
      is_queued = false;
    }
  };
  
  template<class R>
  class cumul_var : public propagator, public prop_inst<cumul_var<R> > {
    typedef prop_inst<cumul_var<R> > I;
    typedef cumul_var<R> P;

    enum ProfileState { P_Invalid = 0, P_Valid = 1, P_Saved = 2 };

    // Typedefs
    typedef unsigned int task_id;
    typedef trailed<V> TrV;
    struct task_info {
      intvar s;
      intvar d;
      R r;
    };

    struct evt_info {
      evt_kind kind;  
      task_id task;
      int t;
      V level;
    };

    struct ex_info {
      task_id t;
      int s;
      int e;
    };

    struct {
      bool operator()(const evt_info& x, const evt_info& y) const {
        if(x.t == y.t) {
          // Process ends before starts.
          return x.kind < y.kind;
        }
        return x.t < y.t;
      }
    } pevt_cmp;

    // Parameters
    vec<task_info> tasks; // We order tasks by decreasing r.
    R cap; // Maximum resource capacity

    // Persistent state
    // Tint active_end;

    p_sparseset profile_tasks;
    p_sparseset active_tasks;

    vec<ex_info> exs;
    char exs_saved;

    // Transient state.
    vec<evt_info> profile;
    boolset lb_change;
    boolset ub_change;
    char profile_state;

    // Helper functions
    inline int est(int xi) const { return lb(tasks[xi].s); }
    inline int eet(int xi) const { return lb(tasks[xi].s) + lb(tasks[xi].d); }
    inline int lst(int xi) const { return ub(tasks[xi].s); }
    inline int let(int xi) const { return ub(tasks[xi].s) + ub(tasks[xi].d); }

    inline V mreq(int xi) const { return lb(tasks[xi].r); }
    inline int mdur(int xi) const { return lb(tasks[xi].d); }

    // For checking.
    int usage_at(int time, const ctx_t& ctx) const {
      V total(0);
      for(const task_info& t : tasks) {
        if(t.s.ub(ctx) <= time && time < t.s.lb(ctx) + t.d.lb(ctx))
          total += t.r.lb(ctx);
      }
      return total;
    }
    bool check_sat(ctx_t& ctx) {
      V max(cap.ub(ctx));
      for(const task_info& t : tasks) {
        if(t.s.lb(ctx) + t.d.lb(ctx) <= t.s.ub(ctx)) {
          // No mandatory component. See if it's blocked by the profile everywhere.
          V req(t.r.lb(ctx));
          for(int ti = t.s.lb(ctx) + t.d.lb(ctx) - 1; ti <= t.s.ub(ctx); ++ti) {
            if(usage_at(t.s.ub(ctx), ctx) <= max - req)
              goto task_placed;
          }
          return false;
        task_placed:
          continue;
        } else {
          // Profile task. Just check for an overload.
          if(t.s.ub(ctx) < t.s.lb(ctx) + t.d.lb(ctx)) {
            if(usage_at(t.s.ub(ctx), ctx) > max)
              return false;
          }
        }
      }
      return true;
    }

    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

    int make_ex(task_id t, int s, int e) {
      this->template save(exs._size(), exs_saved);
      int id = exs.size();
      exs.push(ex_info { t, s, e });
      return id;
    }

    watch_result wake_lb(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_state &= ~(P_Valid);
        queue_prop();
      } else {
        if(lst(ti) < eet(ti)) {
          trail_push(s->persist, profile_tasks.sz);
          profile_tasks.insert(ti);
          profile_state &= ~(P_Valid);
          queue_prop();
        } else if(active_tasks.elem(ti)) {
          lb_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    watch_result wake_ub(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_state &= ~(P_Valid);
        queue_prop();
      } else {
        if(lst(ti) < eet(ti)) {
          trail_push(s->persist, profile_tasks.sz);
          profile_tasks.insert(ti);
          profile_state &= ~(P_Valid);
          queue_prop();
        } else if(active_tasks.elem(ti)) {
          ub_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    watch_result wake_r(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_state &= ~(P_Valid);
        queue_prop();
      } else {
        if(active_tasks.elem(ti)) {
          lb_change.add(ti);
          ub_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    watch_result wake_cap(int _ti) {
      // Don't need to rebuild the profile, but some LST/ESTs
      // may be invalidated.
      profile_state &= ~(P_Valid);
      queue_prop();
      return Wt_Keep;
    }

    void log_ptasks(void) {
      std::cerr << "{";
      for(task_id ti : profile_tasks) {
        std::cerr << ti << ":[" << lst(ti) << "," << eet(ti) << ")|"
          << mreq(ti) << " ";
      }
      std::cerr << "}" << std::endl;
    }

    void log_profile(void) {
      for(evt_info e : profile) {
        std::cerr << e.t << ":" << e.task << ":" << (e.kind == ST ? "+" : "-") << e.level << " ";
      }
      std::cerr << std::endl;
    }

    bool rebuild_profile(vec<clause_elt>& confl) {
#ifdef LOG_PROFILE
      if(s->stats.conflicts > LOG_START_AT) {
      std::cout << "Building profile [" << prop_id << "]:" << std::endl << "-------------------" << std::endl;
      log_ptasks();
      }
#endif

      profile.clear();
      // profile.push(evt_info { ET, INT_MAX, INT_MIN, 0 });
      profile.push(evt_info { ST, INT_MAX, INT_MIN, 0 });
      for(task_id ti : profile_tasks) {
        profile.push(evt_info { ST, ti, lst(ti), mreq(ti) });
        profile.push(evt_info { ET, ti, eet(ti), mreq(ti) });
      }
      std::sort(profile.begin()+1, profile.end(), pevt_cmp);
      profile.push(evt_info { ET, INT_MAX, INT_MAX, 0});

      // Now replace the deltas with actual values

#ifdef LOG_PROFILE
      if(s->stats.conflicts > LOG_START_AT) {
      log_profile();
      }
#endif

      V cumul(0);
      V p_max(0);
      for(evt_info& e : profile) {
        if(e.kind == ST) {
          cumul += e.level;
          if(cumul > p_max) {
            if(cumul > lb(cap)) {
              if(!set_lb(cap, cumul, this->template expl<&P::ex_cap>(e.t, expl_thunk::Ex_BTPRED)))
                return false;
            }
            p_max = cumul;
          }
        } else {
          cumul -= e.level;
        }
        e.level = cumul;
      }

#ifdef LOG_PROFILE
      if(s->stats.conflicts > LOG_START_AT) {
      log_profile();
      std::cerr << std::endl;
      }
#endif

      // Activate any remaining tasks which might
      // be shifted.
      V req_max(ub(cap) - p_max);
      /*
      int ti = active_end;
      if(ti < tasks.size() && mreq(ti) > req_max) {
        trail_push(s->persist, active_tasks.sz);
        active_tasks.insert(ti);
        for(++ti; ti < tasks.size(); ++ti) {
          if(mreq(ti) <= req_max)
            break;
          active_tasks.insert(ti);
        }
        set(active_end, ti);
      }
      */
      bool saved = false;
      for(task_id ti : active_tasks.complement()) {
        if(mreq(ti) > req_max) {
          if(!saved) {
            trail_push(s->persist, active_tasks.sz);
            saved = true;
          }
          active_tasks.insert(ti); 
        }
      }
      return true;
    }

    bool sweep_fwd(task_id ti) {
      // Find the starting interval
      const task_info& t(tasks[ti]);
      if(!(lb(t.d) > 0 && lb(t.r) > 0))
        return true;

      evt_info* s = std::upper_bound(profile.begin(), profile.end(),
        est(ti), [](const int& t, const evt_info& e) { return t <= e.t - (e.kind == ET) ; });
      if(s == profile.end())
        return true;
      // Task stats in the previous interval   
      V lev_max = ub(cap) - mreq(ti);

      int dur = mdur(ti);
      int end_time = est(ti) + dur;
      if(s[-1].task == ti)
        return true;
      int ex_time = s[-1].t;
      V seg_level = s[-1].level;

      while(ex_time < end_time) {
        if(seg_level > lev_max) {
          // Shift start and reset.
          if(!set_lb(t.s, s->t, this->template expl<&P::ex_est>(make_ex(ti, ex_time, s->t), expl_thunk::Ex_BTPRED)))
            return false;
          end_time = s->t + dur;
        }
        // The profile's going to be updated anyway.
        if(s->task == ti)
          return true;
        ex_time = s->t;
        seg_level = s->level;
        ++s;
      }
      return true;
    }

    bool sweep_req(task_id ti) {
      // Find the starting interval
      const task_info& t(tasks[ti]);
      if(!(lb(t.d) > 0 && lb(t.r) > 0))
        return true;

      evt_info* s = std::upper_bound(profile.begin(), profile.end(),
        lst(ti), [](const int& t, const evt_info& e) { return t <= e.t - (e.kind == ET) ; });
      assert(s != profile.end());
      // Task stats in the previous interval   
      int end_time = eet(ti);

      int high_time(s->t);
      V high_level(s->level);

      for(++s; s->t < end_time; ++s) {
        if(high_level < s->level) {
          high_time = s->t;
          high_level = s->level;
        }
      }
      
      V delta(ub(cap) - high_level);
      if(lb(t.r) + delta < ub(t.r)) {
        if(!set_ub(t.r, lb(t.r) + delta,
          this->template expl<&P::ex_req>(make_ex(ti, high_time, 0), expl_thunk::Ex_BTPRED)))
          return false;
      }
      return true;
    }

    bool sweep_bwd(task_id ti) {
#if 0
      return true;
#endif
      // Find the starting interval
      const task_info& t(tasks[ti]);
      if(!(lb(t.d) > 0 && lb(t.r) > 0))
        return true;

      evt_info* s = profile.begin();
      while(s->t - (s->kind == ET) < let(ti)) ++s;
      // evt_info* s = std::upper_bound(profile.begin(), profile.end(),
      //  let(ti), [](const int& t, const evt_info& e) { return t < e.t + (e.kind == ST) ; });
      if(s == profile.begin())
        return true;
      // Task stats in the previous interval   
      V lev_max = ub(cap) - mreq(ti);

      int dur = mdur(ti);
      int start_time = lst(ti);
      int ex_time = s->t;
      if(s->task == ti)
        return true;
      if(ex_time <= start_time) {
        fprintf(stderr, "%% Profile task: %d [%d], %d -> %d.\n",
          s->task, (int) (s - profile.begin()), s->t, s[1].t);
        fprintf(stderr, "%% For task: %d, lst %d duration %d.\n",
          ti, lst(ti), mdur(ti));
      }
      assert(ex_time > start_time);

      --s;
      do {
        assert(ex_time > start_time);
        if(s->task == ti)
          return true;
        if(s->level > lev_max) {
          // Shift start and reset.
          if(!set_ub(t.s, s->t - dur, this->template expl<&P::ex_let>(make_ex(ti, s->t, ex_time), expl_thunk::Ex_BTPRED)))
            return false;
          start_time = s->t - dur;
        }
        // The profile's going to be updated anyway.
        ex_time = s->t;
        --s;
      } while(ex_time > start_time);
      return true;
    }

    inline void EX_PUSH(vec<clause_elt>& expl, patom_t at) {
      assert(!ub(at));
      expl.push(at);
    }

    void ex_est(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);
      // int t_est(std::max(t.s.lb_of_pval(p), e.ex_time+1));
      // int t_est(std::max(t.s.lb_of_pval(p), e.ex_time+1));

      // Assumption: we're doing stepwise-propagation.
      // So at this point, lb(t.s) < est, and every task
      // active at (est-1) was active from lb(t.s) + dur - 1.
      
      // So, we collect a sufficient set of tasks, active at
      // (est-1).
      V e_req = ub(cap) - mreq(ti);
      vec<task_id> etasks;
      for(task_id p : profile_tasks) {
        if(lst(p) <= e.s && e.e <= eet(p)) {
          if(p == ti)
            continue;
          // assert(lst(p) >= lb(t.s));

          etasks.push(p);
          if(e_req < mreq(p)) {
            // Found a cover. Minimize, and find a relaxed
            // lb for t.
            V slack = mreq(p) - e_req;
            
            int jj = 0;
            for(int ii = 0; ii < etasks.size(); ++ii) {
              if(mreq(p) < slack) {
                slack -= mreq(p);
                continue;
              }
              etasks[jj++] = etasks[ii];
            }
            etasks.shrink_(etasks.size() - jj);
            // Now construct the actual explanation
            // Either t is entirely before earliest...
#if 1
            EX_PUSH(expl, t.s <= e.s - mdur(ti));
            EX_PUSH(expl, t.r < mreq(ti));
            EX_PUSH(expl, t.d < mdur(ti));
            EX_PUSH(expl, cap >= ub(cap) + slack);
            // ...or some member of etasks doesn't cover.
            for(task_id p : etasks) {
              EX_PUSH(expl, tasks[p].s > e.s);
              EX_PUSH(expl, tasks[p].s < e.e - mdur(p));

              EX_PUSH(expl, tasks[p].d < mdur(p));
              EX_PUSH(expl, tasks[p].r < mreq(p));
            }
#else
            // Semi-naive explanation
            expl.push(t.s < lb(t.s));
            for(task_id p : etasks) {
              expl.push(tasks[p].s < lb(tasks[p].s));
              expl.push(tasks[p].s > ub(tasks[p].s));
            }
#endif
            return;
          }
          e_req -= mreq(p);
        }
      }
      // Should be unreachable
      GEAS_ERROR;
    }
    
    void ex_let(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);
      // int t_let(std::min(t.s.ub_of_pval(p) + mdur(ti), e.ex_time));

      V e_req = (ub(cap) - mreq(ti));
      vec<task_id> etasks;
      for(task_id p : profile_tasks) {
        if(lst(p) <= e.s && e.e <= eet(p)) {
          // assert(p != ti);
          if(p == ti)
            continue;
          // assert(lst(p) >= lb(t.s));

          etasks.push(p);
          if(e_req < mreq(p)) {
            // Found a cover. Minimize, and find a relaxed
            // lb for t.
            V slack = mreq(p) - e_req;
            
            int jj = 0;
            for(int ii = 0; ii < etasks.size(); ++ii) {
              if(mreq(p) < slack) {
                slack -= mreq(p);
                continue;
              }
              etasks[jj++] = etasks[ii];
            }
            etasks.shrink_(etasks.size() - jj);
            // Now construct the actual explanation
#if 1
            // Either t is pushed after e.ex_time...
            EX_PUSH(expl, t.s >= e.e);
            EX_PUSH(expl, t.r < mreq(ti));
            EX_PUSH(expl, t.d < mdur(ti));
            // ...or some member of etasks doesn't cover.
            for(task_id p : etasks) {
              // EX_PUSH(expl, tasks[p].s >= e.ex_time);
              // EX_PUSH(expl, tasks[p].s < t_let - tasks[p].d);
              EX_PUSH(expl, tasks[p].s > e.s);
              EX_PUSH(expl, tasks[p].s < e.e - mdur(p));
              EX_PUSH(expl, tasks[p].d < mdur(p));
              EX_PUSH(expl, tasks[p].r < mreq(p));
            }
            EX_PUSH(expl, cap >= ub(cap) + slack);
#else
            // Semi-naive explanation
            expl.push(t.s > ub(t.s));
            for(task_id p : etasks) {
              expl.push(tasks[p].s < lb(tasks[p].s));
              expl.push(tasks[p].s > ub(tasks[p].s));
            }
#endif
            return;
          }
          e_req -= mreq(p);
        }
      }
      // Should be unreachable
      GEAS_ERROR;
    }

    template<bool Strict>
    bool cmp(V x, V y) const {
      return Strict ? (x < y) : !(y < x);
    }

    template<bool Strict>
    V explain_usage(int t_ex, int s, int e, V req_use, vec<clause_elt>& expl) {
      V remaining(req_use);
      vec<task_id> e_tasks;
      for(task_id p : profile_tasks) {
        if(p == (task_id) t_ex)
          continue;  
        if(lst(p) <= s && e <= eet(p)) {
          e_tasks.push(p);
          if(cmp<Strict>(remaining, mreq(p))) {
            // Collected sufficient.
            V slack(mreq(p) - remaining);
            
            // Collect only tasks which are needed
            for(task_id t : e_tasks) {
              if(cmp<Strict>(mreq(t), slack)) {
                slack -= mreq(t);
                continue;
              }
              EX_PUSH(expl, tasks[t].s <= s - mdur(t));
              EX_PUSH(expl, tasks[t].s >= e);
              EX_PUSH(expl, tasks[t].d < mdur(t));
              EX_PUSH(expl, tasks[t].r < mreq(t));
            }
            return req_use + slack;
          }
          remaining -= mreq(p);
        }
      }
      // Not enough usage over the profile region.
      GEAS_ERROR;
      return 0;
    }

    void ex_req(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);
      
      V r_max(tasks[ti].r.ub_of_pval(p)); 
      V r_ex(explain_usage<false>(ti, e.s, e.s+1, ub(cap) - r_max, expl));
      EX_PUSH(expl, t.s <= e.s - mdur(ti)); 
      EX_PUSH(expl, t.s > e.s);
      EX_PUSH(expl, cap > r_ex + r_max);
    }

    void ex_cap(int t, pval_t p, vec<clause_elt>& expl) {
      V to_cover(cap.lb_of_pval(p));
      // Usual trick: collect a sufficient set of tasks, then
      // discard until we have a minimal set.
      vec<task_id> e_tasks;
      for(task_id p : profile_tasks) {
        if(lst(p) <= t && t < eet(p)) {
          e_tasks.push(p);
          if(to_cover <= mreq(p)) {
            // Found a sufficient cover.
            V slack(mreq(p) - to_cover);
            for(task_id q : e_tasks) {
              // Can be omitted; we have sufficient
              // slack later on.
              if(mreq(q) <= slack) {
                slack -= mreq(q);
                continue;
              }
              expl.push(tasks[q].s <= t - mdur(q));
              expl.push(tasks[q].s > t);
              expl.push(tasks[q].d < mdur(q));
              expl.push(tasks[q].r < mreq(q));
            }
            return;
          }
          to_cover -= mreq(p);
        }
      }
      GEAS_ERROR;
    }

  public:
    cumul_var(solver_data* s, vec<intvar>& starts, vec<intvar>& dur, vec<R>& res, R _cap)
      : propagator(s), cap(_cap)
      // , active_end(0)
      , profile_tasks(starts.size())
      , active_tasks(0)
      , exs_saved(false)
      , lb_change(starts.size())
      , ub_change(starts.size())
      , profile_state(P_Invalid) {
      int rMax(ub(cap));
      for(int xi : irange(starts.size())) {
        // Skip any tasks which are definitely irrelevant.
        if(!ub(dur[xi]) || !ub(res[xi]))
          continue;
        if(lb(res[xi]) > rMax)
          throw RootFail();
        task_info t(task_info { starts[xi], dur[xi], res[xi] });
        tasks.push(t);
      }
      active_tasks.growTo_strict(tasks.size());
      for(int xi: irange(tasks.size())) {
        task_info& t(tasks[xi]);
        t.s.attach(E_LB, this->template watch<&P::wake_lb>(xi));
        t.s.attach(E_UB, this->template watch<&P::wake_ub>(xi));

        t.d.attach(E_LB, this->template watch<&P::wake_lb>(xi));
        t.r.attach(s, E_LB, this->template watch<&P::wake_r>(xi));
        if(lst(xi) < eet(xi)) {
          profile_tasks.insert(xi);
        }
      }
      cap.attach(s, E_UB, this->template watch<&P::wake_cap>(0));
    }

    bool propagate(vec<clause_elt>& confl) {
      // fprintf(stderr, "Active: %d of %d\n", active_tasks.size(), tasks.size());
      if(!(profile_state & P_Valid)) {
        if(!(profile_state & P_Saved))
          s->persist.bt_flags.push(&profile_state);
        if(!rebuild_profile(confl))
          return false;
#if 1
        for(task_id t : active_tasks) {
          if(is_fixed(tasks[t].s))
            continue;
          if(!sweep_fwd(t))
            return false;
          if(!sweep_bwd(t))
            return false;   
        }
        for(task_id t : profile_tasks) {
          if(lb(tasks[t].r) < ub(tasks[t].r) && !sweep_req(t))
            return false;
        }
#endif
      } else {
        // If the profile hasn't changed, only sweep
        // variables with updated bounds.
#if 1
        for(task_id t : lb_change) {
          if(is_fixed(tasks[t].s))
            continue;
          if(!sweep_fwd(t))
            return false;
        }
        for(task_id t : ub_change) {
          if(is_fixed(tasks[t].s))
            continue;
          if(!sweep_bwd(t))
            return false;
        }
#endif
      }
      return true;
    }

    void cleanup(void) {
      lb_change.clear();
      ub_change.clear();
      is_queued = false;
    }
  };

  // Lighter-weight version of cumulative-TT.
  template<class R>
  class cumul_var_lw : public propagator, public prop_inst<cumul_var_lw<R> > {
    typedef prop_inst<cumul_var_lw<R> > I;
    typedef cumul_var_lw<R> P;

    enum ProfileState { P_Invalid = 0, P_Valid = 1, P_Saved = 2 };

    // Typedefs
    typedef unsigned int task_id;
    typedef trailed<V> TrV;
    struct task_info {
      intvar s;
      intvar d;
      R r;
    };

    struct By_ECT {
      typedef task_info Var;
      typedef int Val;
      static void attach(solver_data* s, task_info& t, watch_callback c) {
        t.s.attach(s, E_LB, c);
        t.d.attach(s, E_LB, c);
      }
      static Val eval(solver_data* s, const Var& t) { return t.s.lb(s) + t.d.lb(s); }
      static bool compare(Val p, Val q) { return p < q; }
    };

    struct ex_info {
      task_id t;
      int s;
      int e;
    };
    
    // Parameters
    vec<task_info> tasks; // We order tasks by decreasing r.
    R cap; // Maximum resource capacity

    // Persistent state
    p_sparseset profile_tasks;
    p_sparseset active_tasks;

    vec<ex_info> exs;
    char exs_saved;

  /*
    OrderedPerm< By_UB<intvar> > by_lst;
    OrderedPerm< By_ECT > by_ect;
    */

    // Transient state.
    // Profile info.
    int nb;
    int* bounds;
    // V* delta;
    V* height;

    int* lst_rank;
    int* ect_rank;
    int* est_residue;
    int* lct_residue; 

    unsigned int* ect_ord;
    unsigned int* lst_ord;

    boolset lb_change;
    boolset ub_change;
    char profile_state;

    // Helper functions
    inline int est(int xi) const { return lb(tasks[xi].s); }
    inline int ect(int xi) const { return lb(tasks[xi].s) + lb(tasks[xi].d); }
    inline int lst(int xi) const { return ub(tasks[xi].s); }
    inline int let(int xi) const { return ub(tasks[xi].s) + ub(tasks[xi].d); }
    inline int ldct(int xi) const { return ub(tasks[xi].s) + lb(tasks[xi].d); }

    inline V mreq(int xi) const { return lb(tasks[xi].r); }
    inline int mdur(int xi) const { return lb(tasks[xi].d); }

    // For checking.
    int usage_at(int time, const ctx_t& ctx) const {
      V total(0);
      for(const task_info& t : tasks) {
        if(t.s.ub(ctx) <= time && time < t.s.lb(ctx) + t.d.lb(ctx))
          total += t.r.lb(ctx);
      }
      return total;
    }
    bool check_sat(ctx_t& ctx) {
      V max(cap.ub(ctx));
      for(const task_info& t : tasks) {
        if(t.s.lb(ctx) + t.d.lb(ctx) <= t.s.ub(ctx)) {
          // No mandatory component. See if it's blocked by the profile everywhere.
          V req(t.r.lb(ctx));
          for(int ti = t.s.lb(ctx) + t.d.lb(ctx) - 1; ti <= t.s.ub(ctx); ++ti) {
            if(usage_at(t.s.ub(ctx), ctx) <= max - req)
              goto task_placed;
          }
          return false;
        task_placed:
          continue;
        } else {
          // Profile task. Just check for an overload.
          if(t.s.ub(ctx) < t.s.lb(ctx) + t.d.lb(ctx)) {
            if(usage_at(t.s.ub(ctx), ctx) > max)
              return false;
          }
        }
      }
      return true;
    }

    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

    int make_ex(task_id t, int s, int e) {
      this->template save(exs._size(), exs_saved);
      int id = exs.size();
      exs.push(ex_info { t, s, e });
      return id;
    }

    watch_result wake_lb(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_state &= ~(P_Valid);
        queue_prop();
      } else {
        if(lst(ti) < ect(ti)) {
          trail_push(s->persist, profile_tasks.sz);
          profile_tasks.insert(ti);
          profile_state &= ~(P_Valid);
          queue_prop();
        } else if(active_tasks.elem(ti)) {
          lb_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    watch_result wake_ub(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_state &= ~(P_Valid);
        queue_prop();
      } else {
        if(lst(ti) < ect(ti)) {
          trail_push(s->persist, profile_tasks.sz);
          profile_tasks.insert(ti);
          profile_state &= ~(P_Valid);
          queue_prop();
        } else if(active_tasks.elem(ti)) {
          ub_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    watch_result wake_r(int ti) {
      if(profile_tasks.elem(ti)) {
        profile_state &= ~(P_Valid);
        queue_prop();
      } else {
        if(active_tasks.elem(ti)) {
          lb_change.add(ti);
          ub_change.add(ti);
          queue_prop();
        }
      }
      return Wt_Keep;
    }

    watch_result wake_cap(int _ti) {
      // Don't need to rebuild the profile, but some LST/ESTs
      // may be invalidated.
      profile_state &= ~(P_Valid);
      queue_prop();
      return Wt_Keep;
    }

    void log_ptasks(void) {
      std::cerr << "{";
      for(task_id ti : profile_tasks) {
        std::cerr << ti << ":[" << lst(ti) << "," << ect(ti) << ")|"
          << mreq(ti) << " ";
      }
      std::cerr << "}" << std::endl;
    }

    void log_profile(void) {
      for(int ii = 0; ii < nb; ++ii) {
        std::cerr << bounds[ii] << ":" << height[ii];
      }
      std::cerr << std::endl;
    }

    bool rebuild_profile(vec<clause_elt>& confl) {
#ifdef LOG_PROFILE
      if(s->stats.conflicts > LOG_START_AT) {
      std::cout << "Building profile [" << prop_id << "]:" << std::endl << "-------------------" << std::endl;
      log_ptasks();
      }
#endif

      // Set up the landmarks.
      /*
      vec<unsigned int>& lst_ord(by_lst.get());
      vec<unsigned int>& ect_ord(by_ect.get());
      */
      int sz = 0;
      for(int t : profile_tasks) {
        lst_ord[sz] = t;
        ect_ord[sz] = t;
        ++sz;
      }
      std::sort(lst_ord, lst_ord+sz,
        [&](int u, int v) { return lst(u) < lst(v); });
      std::sort(ect_ord, ect_ord+sz,
        [&](int u, int v) { return ect(u) < ect(v); });

      bounds[0] = INT_MIN;
      height[0] = 0;
      if(profile_tasks.size() == 0) {
        nb = 0;
        return true;
      }

      int b(lst(lst_ord[0]));
      bounds[1] = b;
      V ht(0);

      int maxT(INT_MIN);
      V maxHt(0);

      nb = 1;
      unsigned int* u_it(ect_ord);
      int u_b(ect(*u_it));

      for(unsigned int ii : range(lst_ord, lst_ord+sz)) {
        int l_i(lst(ii));
        // Process any upper bounds which are _strictly_ below the next lb.
        while(u_b < l_i) {
          if(b < u_b) {
            height[nb] = ht;
            if(maxHt < ht) {
              maxT = b;
              maxHt = ht;
            }
            ++nb;
            bounds[nb] = b = u_b;
          }
          ect_rank[*u_it] = nb;
          ht -= mreq(*u_it);
          ++u_it;
          u_b = ect(*u_it);
        }
        // And now do the lb.
        if(b < l_i) {
          height[nb] = ht;
          if(maxHt < ht) {
            maxT = b;
            maxHt = ht;
          }
          ++nb;
          bounds[nb] = b = l_i;
        }
        lst_rank[ii] = nb;
        ht += mreq(ii);
      }
      // Now process the remaining upper bounds.
      unsigned int* ect_end = ect_ord+sz;
      for(; u_it < ect_end ; ++u_it) {
        u_b = ect(*u_it);
        if(b < u_b) {
          height[nb] = ht;
          if(maxHt < ht) {
            maxT = b;
            maxHt = ht;
          }
          ++nb;
          bounds[nb] = b = u_b;
        }
        ect_rank[*u_it] = nb;
        ht -= mreq(*u_it);
      }
      height[nb] = ht; // Should be zero
      bounds[nb+1] = INT_MAX;
      height[nb+1] = 0;

      // Check the profile.
#if 0
      for(int ii = 1; ii < nb; ++ii) {
        int sum = 0;
        for(int p : profile_tasks) {
          if(lst(p) <= bounds[ii] && bounds[ii+1] <= ect(p))
            sum += mreq(p);
        }
        assert(sum == height[ii]);
      }
      for(int p : profile_tasks) {
        assert(bounds[lst_rank[p]] == lst(p));
        assert(bounds[ect_rank[p]] == ect(p));
      }
#endif
#ifdef LOG_PROFILE
      if(s->stats.conflicts > LOG_START_AT) {
      log_profile();
      std::cerr << std::endl;
      }
#endif

      UPDATE_LB(cap, maxHt,
        this->template expl<&P::ex_cap>(maxT, expl_thunk::Ex_BTPRED));

      // Activate any remaining tasks which might
      // be shifted.
      V req_max(ub(cap) - maxHt);
      bool saved = false;
      for(task_id ti : active_tasks.complement()) {
        if(mreq(ti) > req_max) {
          if(!saved) {
            trail_push(s->persist, active_tasks.sz);
            saved = true;
          }
          active_tasks.insert(ti); 
        }
      }
      return true;
    }

    // Find the profile rectangle containing t,
    // using hint.
    int find_rank(int t, int hint) {
      int p(std::min(hint, nb));
      // Binary search, starting from p.
      int low(0);
      int high(nb);
      do {
        if(t < bounds[p]) {
          // t is left of p.
          high = p-1;
        } else if(bounds[p+1] <= t) {
          low = p+1;
        } else {
          return p;
        }
        p = low + (high - low)/2;
      } while (low < high);
      // assert(low == high);
      return low;
    }

    bool sweep_fwd(task_id ti) {
      // Find the starting interval
      const task_info& t(tasks[ti]);
      if(!(lb(t.d) > 0 && lb(t.r) > 0))
        return true;

      // Find the rank of the EST.
      int est_t = est(ti);
      int s = est_residue[ti] = find_rank(est_t, est_residue[ti]);
      // Stop at the mandatory region, if one exists.
      int s_E = profile_tasks.elem(ti) ? lst_rank[ti] : nb;

      int d_t = mdur(ti);
      int ect_t(est_t + d_t);

      V lev_max = ub(cap) - mreq(ti);

      for(; s < s_E; ++s) {
        if(ect_t <= bounds[s])
          break;
        if(lev_max < height[s]) {
          est_t = bounds[s+1];
          ect_t = est_t + d_t;

          UPDATE_LB(tasks[ti].s, est_t, 
              this->template expl<&P::ex_est>(make_ex(ti, bounds[s], bounds[s+1]), expl_thunk::Ex_BTPRED));
        }
      }
      return true;
    }

    bool sweep_bwd(task_id ti) {
      // Find the starting interval
      const task_info& t(tasks[ti]);
      if(!(lb(t.d) > 0 && lb(t.r) > 0))
        return true;

      // Find the rank of the EST.
      int lct_t = ldct(ti);
      int e = lct_residue[ti] = find_rank(lct_t-1, lct_residue[ti]);
      int e_B = profile_tasks.elem(ti) ? ect_rank[ti] : 1;

      int d_t = mdur(ti);
      int lst_t(lct_t - d_t);

      V lev_max = ub(cap) - mreq(ti);

      for(; e_B <= e; --e) {
        if(lev_max < height[e]) {
          lct_t = bounds[e];
          lst_t = lct_t - d_t;

          UPDATE_UB(tasks[ti].s, lst_t,
              this->template expl<&P::ex_lst>(make_ex(ti, bounds[e], bounds[e+1]), expl_thunk::Ex_BTPRED));
        }
        if(bounds[e] <= lst_t)
          break;
      }
      return true;
    }

    bool sweep_req(task_id ti) {
      // Find the starting interval
      const task_info& t(tasks[ti]);
      if(!(lb(t.d) > 0 && lb(t.r) > 0))
        return true;

      int s = lst_rank[ti];
      int e = ect_rank[ti];
      int h = s;
      V h_ht = height[s];
      for(++s; s < e; ++s) {
        if(h_ht < height[s]) {
          h = s;
          h_ht = height[s];
        }
      }
      V delta(ub(cap) - h_ht);
      UPDATE_UB(t.r, lb(t.r) + delta,
        this->template expl<&P::ex_req>(make_ex(ti, bounds[h], 0), expl_thunk::Ex_BTPRED));
      return true;
    }

    void ex_est(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);

      // Assumption: we're doing stepwise-propagation.
      // So at this point, lb(t.s) < est, and every task
      // active at (est-1) was active from lb(t.s) + dur - 1.
      
      // So, we collect a sufficient set of tasks, active at
      // (est-1).
      //int e_e = std::max(e.s+1, t.s.lb_of_pval(p));

      V e_req = ub(cap) - mreq(ti);
      vec<task_id> etasks;
      for(task_id p : profile_tasks) {
        if(lst(p) <= e.s && e.e <= ect(p)) {
          if(p == ti)
            continue;

          etasks.push(p);
          if(e_req < mreq(p)) {
            // Found a cover. Minimize, and find a relaxed
            // lb for t.
            V slack = mreq(p) - e_req;
            
            int jj = 0;
            for(int ii = 0; ii < etasks.size(); ++ii) {
              if(mreq(p) < slack) {
                slack -= mreq(p);
                continue;
              }
              etasks[jj++] = etasks[ii];
            }
            etasks.shrink_(etasks.size() - jj);
            // Now construct the actual explanation
            // Either t is entirely before earliest...
            EX_PUSH(expl, t.s <= e.s - mdur(ti));
            EX_PUSH(expl, t.r < mreq(ti));
            EX_PUSH(expl, t.d < mdur(ti));
            EX_PUSH(expl, cap >= ub(cap) + slack);
            // ...or some member of etasks doesn't cover.
            for(task_id p : etasks) {
              EX_PUSH(expl, tasks[p].s > e.s);
              EX_PUSH(expl, tasks[p].s < e.e - mdur(p));

              EX_PUSH(expl, tasks[p].d < mdur(p));
              EX_PUSH(expl, tasks[p].r < mreq(p));
            }
            return;
          }
          e_req -= mreq(p);
        }
      }
      // Should be unreachable
      GEAS_ERROR;
    }
    
    void ex_lst(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);
      // int t_let(std::min(t.s.ub_of_pval(p) + mdur(ti), e.ex_time));

      // int e_s = std::min(e.e-1, t.s.ub_of_pval(p) + mdur(ti));
      V e_req = (ub(cap) - mreq(ti));
      vec<task_id> etasks;
      for(task_id p : profile_tasks) {
        if(lst(p) <= e.s && e.e <= ect(p)) {
          // assert(p != ti);
          if(p == ti)
            continue;
          // assert(lst(p) >= lb(t.s));

          etasks.push(p);
          if(e_req < mreq(p)) {
            // Found a cover. Minimize, and find a relaxed
            // lb for t.
            V slack = mreq(p) - e_req;
            
            int jj = 0;
            for(int ii = 0; ii < etasks.size(); ++ii) {
              if(mreq(p) < slack) {
                slack -= mreq(p);
                continue;
              }
              etasks[jj++] = etasks[ii];
            }
            etasks.shrink_(etasks.size() - jj);
            // Now construct the actual explanation
            // Either t is pushed after e.ex_time...
            EX_PUSH(expl, t.s >= e.e);
            EX_PUSH(expl, t.r < mreq(ti));
            EX_PUSH(expl, t.d < mdur(ti));
            // ...or some member of etasks doesn't cover.
            for(task_id p : etasks) {
              // EX_PUSH(expl, tasks[p].s >= e.ex_time);
              // EX_PUSH(expl, tasks[p].s < t_let - tasks[p].d);
              EX_PUSH(expl, tasks[p].s > e.s);
              EX_PUSH(expl, tasks[p].s < e.e - mdur(p));
              EX_PUSH(expl, tasks[p].d < mdur(p));
              EX_PUSH(expl, tasks[p].r < mreq(p));
            }
            EX_PUSH(expl, cap >= ub(cap) + slack);
            return;
          }
          e_req -= mreq(p);
        }
      }
      // Should be unreachable
      GEAS_ERROR;
    }

    template<bool Strict>
    bool cmp(V x, V y) const {
      return Strict ? (x < y) : !(y < x);
    }

    template<bool Strict>
    V explain_usage(int t_ex, int s, int e, V req_use, vec<clause_elt>& expl) {
      V remaining(req_use);
      vec<task_id> e_tasks;
      for(task_id p : profile_tasks) {
        if(p == (task_id) t_ex)
          continue;  
        if(lst(p) <= s && e <= ect(p)) {
          e_tasks.push(p);
          if(cmp<Strict>(remaining, mreq(p))) {
            // Collected sufficient.
            V slack(mreq(p) - remaining);
            
            // Collect only tasks which are needed
            for(task_id t : e_tasks) {
              if(cmp<Strict>(mreq(t), slack)) {
                slack -= mreq(t);
                continue;
              }
              EX_PUSH(expl, tasks[t].s <= s - mdur(t));
              EX_PUSH(expl, tasks[t].s >= e);
              EX_PUSH(expl, tasks[t].d < mdur(t));
              EX_PUSH(expl, tasks[t].r < mreq(t));
            }
            return req_use + slack;
          }
          remaining -= mreq(p);
        }
      }
      // Not enough usage over the profile region.
      GEAS_ERROR;
      return 0;
    }

    void ex_req(int ex_id, pval_t p, vec<clause_elt>& expl) {
      ex_info e(exs[ex_id]);
      task_id ti(e.t);
      const task_info& t(tasks[ti]);
      
      V r_max(tasks[ti].r.ub_of_pval(p)); 
      V r_ex(explain_usage<false>(ti, e.s, e.s+1, ub(cap) - r_max, expl));
      EX_PUSH(expl, t.s <= e.s - mdur(ti)); 
      EX_PUSH(expl, t.s > e.s);
      EX_PUSH(expl, cap > r_ex + r_max);
    }

    void ex_cap(int t, pval_t p, vec<clause_elt>& expl) {
      V to_cover(cap.lb_of_pval(p));
      // Usual trick: collect a sufficient set of tasks, then
      // discard until we have a minimal set.
      vec<task_id> e_tasks;
      for(task_id p : profile_tasks) {
        if(lst(p) <= t && t < ect(p)) {
          e_tasks.push(p);
          if(to_cover <= mreq(p)) {
            // Found a sufficient cover.
            V slack(mreq(p) - to_cover);
            for(task_id q : e_tasks) {
              // Can be omitted; we have sufficient
              // slack later on.
              if(mreq(q) <= slack) {
                slack -= mreq(q);
                continue;
              }
              expl.push(tasks[q].s <= t - mdur(q));
              expl.push(tasks[q].s > t);
              expl.push(tasks[q].d < mdur(q));
              expl.push(tasks[q].r < mreq(q));
            }
            return;
          }
          to_cover -= mreq(p);
        }
      }
      GEAS_ERROR;
    }

  public:
    cumul_var_lw(solver_data* s, vec<intvar>& starts, vec<intvar>& dur, vec<R>& res, R _cap)
      : propagator(s), cap(_cap)
      // , active_end(0)
      , profile_tasks(starts.size())
      , active_tasks(0)
      , exs_saved(false)
      , bounds(new int[2 * starts.size() + 2])
      , height(new int[2 * starts.size() + 2])
      , lst_rank(new int[starts.size()])
      , ect_rank(new int[starts.size()])
      , est_residue(new int[starts.size()])
      , lct_residue(new int[starts.size()])
      , ect_ord(new unsigned int[starts.size()])
      , lst_ord(new unsigned int[starts.size()])
      , lb_change(starts.size())
      , ub_change(starts.size())
      , profile_state(P_Invalid) {
      memset(est_residue, 0, sizeof(int) * starts.size());
      memset(lct_residue, 0, sizeof(int) * starts.size());
      int rMax(ub(cap));
      for(int xi : irange(starts.size())) {
        // Skip any tasks which are definitely irrelevant.
        if(!ub(dur[xi]) || !ub(res[xi]))
          continue;
        if(lb(res[xi]) > rMax)
          throw RootFail();
        task_info t(task_info { starts[xi], dur[xi], res[xi] });
        tasks.push(t);
      }
      active_tasks.growTo_strict(tasks.size());
      for(int xi: irange(tasks.size())) {
        task_info& t(tasks[xi]);
        t.s.attach(E_LB, this->template watch<&P::wake_lb>(xi));
        t.s.attach(E_UB, this->template watch<&P::wake_ub>(xi));

        t.d.attach(E_LB, this->template watch<&P::wake_lb>(xi));
        t.r.attach(s, E_LB, this->template watch<&P::wake_r>(xi));
        if(lst(xi) < ect(xi)) {
          profile_tasks.insert(xi);
        }
      }
      cap.attach(s, E_UB, this->template watch<&P::wake_cap>(0));
    }

    bool propagate(vec<clause_elt>& confl) {
      // fprintf(stderr, "%% [%d] Active: %d of %d\n", prop_id, active_tasks.size(), tasks.size());
      if(!(profile_state & P_Valid)) {
        if(!(profile_state & P_Saved))
          s->persist.bt_flags.push(&profile_state);
        if(!rebuild_profile(confl))
          return false;

        for(task_id t : active_tasks) {
          if(is_fixed(tasks[t].s))
            continue;
          if(!sweep_fwd(t))
            return false;
          if(!sweep_bwd(t))
            return false;   
        }
        for(task_id t : profile_tasks) {
          if(lb(tasks[t].r) < ub(tasks[t].r) && !sweep_req(t))
            return false;
        }
      } else {
        // If the profile hasn't changed, only sweep
        // variables with updated bounds.
        for(task_id t : lb_change) {
          if(is_fixed(tasks[t].s))
            continue;
          if(!sweep_fwd(t))
            return false;
        }
        for(task_id t : ub_change) {
          if(is_fixed(tasks[t].s))
            continue;
          if(!sweep_bwd(t))
            return false;
        }
      }
      return true;
    }

    void cleanup(void) {
      lb_change.clear();
      ub_change.clear();
      is_queued = false;
    }
  };

  template<class R>
  class cumul_TL : public propagator, public prop_inst<cumul_TL<R> > {
    typedef prop_inst<cumul_TL<R> > I;
    typedef cumul_TL<R> P;

    enum ProfileState { P_Invalid = 0, P_Valid = 1, P_Saved = 2 };

    // Typedefs
    typedef unsigned int task_id;
    typedef trailed<V> TrV;
    struct task_info {
      intvar s;
      intvar d;
      R r;
    };

    struct By_LCT {
      typedef task_info Var;
      typedef int Val;
      static void attach(solver_data* s, task_info& t, watch_callback c) {
        t.s.attach(s, E_UB, c);
        t.d.attach(s, E_LB, c);
      }
      static Val eval(solver_data* s, const Var& t) { return t.s.ub(s) + t.d.lb(s); }
      static bool compare(Val p, Val q) { return p < q; }
    };


    // Parameters
    vec<task_info> tasks; // We order tasks by decreasing r.
    R cap; // Maximum resource capacity

    // Transient state
    // vec<unsigned int> est_ord;
    OrderedPerm< By_LB<intvar> > by_est;
    OrderedPerm<By_LCT> by_lct;
    // vec<unsigned int> lct_ord;
    int nb;
    int* bounds; // Has capacity 2 * |Vars| + 2
    int* d; // Critical capacity deltas
    int* t; // Critical capacity pointers
    int* h; // Hall interval pointers
    // Capacity |Vars|
    int* minrank;
    int* maxrank;
    V eMax; // Upper bound on energy over the schedule.

    // Helper functions
    inline int est(ctx_t& ctx, int xi) const { return tasks[xi].s.lb(ctx); }
    inline int lst(ctx_t& ctx, int xi) const { return tasks[xi].s.uu(ctx); }
    inline int ldct(ctx_t& ctx, int xi) const { return tasks[xi].s.ub(ctx) + tasks[xi].d.lb(ctx); }

    inline int est(int xi) const { return lb(tasks[xi].s); }
    inline int eet(int xi) const { return lb(tasks[xi].s) + lb(tasks[xi].d); }
    inline int lst(int xi) const { return ub(tasks[xi].s); }
    inline int let(int xi) const { return ub(tasks[xi].s) + ub(tasks[xi].d); }

    // Latest completion time of the definite component.
    inline int ldct(int xi) const { return ub(tasks[xi].s) + lb(tasks[xi].d); }

    inline V mreq(int xi) const { return lb(tasks[xi].r); }
    inline int mdur(int xi) const { return lb(tasks[xi].d); }

    // For checking.
    int usage_at(int time, const ctx_t& ctx) const {
      V total(0);
      for(const task_info& t : tasks) {
        if(t.s.ub(ctx) <= time && time < t.s.lb(ctx) + t.d.lb(ctx))
          total += t.r.lb(ctx);
      }
      return total;
    }

    V compute_env(ctx_t& ctx, int l, int u) {
      V energy(0);
      for(const task_info& t : tasks) {
        if(l <= t.s.lb(ctx) && t.s.ub(ctx) + t.d.lb(ctx) <= u) {
          energy += t.d.lb(ctx) * t.r.lb(ctx);
        }
      }
      return energy;
    }

    bool check_sat(ctx_t& ctx) {
      V max(cap.ub(ctx));
      
      vec<int> starts;
      vec<int> ends;
      for(int t : irange(tasks.size())) {
        starts.push(est(ctx, t));
        ends.push(ldct(ctx, t));
      }
      uniq(starts);
      uniq(ends);
            
      for(int s : starts) {
        for(int e : ends) {
          if(e <= s)
            continue;
          if(max * (e - s) < compute_env(ctx, s, e))
            return false;
        }
      }
      return true;
    }

    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }


    void report_internal(void) {

    }

    template<class E>
    void ex_env(int st, int e, E& expl) {
      V cMax(ub(cap));
      V env(cMax * (e - st));

      for(int t : irange(tasks.size())) {
        int dT(lb(tasks[t].d));

        if(est(t) < st)
          continue;
        if(e < lst(t) + dT)
          continue;

        V dR(lb(tasks[t].r));
        EX_PUSH(expl, tasks[t].s < st);
        EX_PUSH(expl, tasks[t].s > e - dT);
        EX_PUSH(expl, tasks[t].d < dT);
        EX_PUSH(expl, tasks[t].r < dR);
        V eT(dR * dT);
        if(env < eT) {
          // We have a valid explanation. We could, potentially, relax cMax.
          // But won't for now.
          EX_PUSH(expl, cap > cMax);
          return;
        } else {
          env -= eT;
        }
      }
      GEAS_ERROR;
    }

    template<class E>
    void ex_env_l(int e, E& expl) {
      V cMax(ub(cap));
      V env(0);
      
      // Assumes est_ord is up to date.
      const vec<unsigned int>& est_ord(by_est.get());

      vec<unsigned int> ex_tasks;
      for(int ti = est_ord.size()-1; ti >= 0; --ti) {
        int t(est_ord[ti]);
        if(ldct(t) > e)
          continue;
        ex_tasks.push(t);
        env += mdur(t) * mreq(t);
        if(cMax * (e - est(t)) < env) {
          // Found our envelope.
          int s = est(t); // FIXME: Relax.
          EX_PUSH(expl, cap > cMax);
          for(int u : ex_tasks) {
            int dU(mdur(u));
            V dR(mreq(u));
            EX_PUSH(expl, tasks[u].s < s);
            EX_PUSH(expl, tasks[u].s > e - dU);
            EX_PUSH(expl, tasks[u].d < dU);
            EX_PUSH(expl, tasks[u].r < dR);
          }
          return;
        }
      }
      GEAS_ERROR;
    }

    static int pathmax(int* p, int k) {
      while(k < p[k])
        k = p[k];
      return k;
    }
    static int pathmin(int* p, int k) {
      while(k > p[k])
        k = p[k];
      return k;
    }
    static void pathset(int* a, int x, int y, int z) {
      int o = a[x];
      while(x != y) {
        a[x] = z;
        x = o;
        o = a[x];
      }
    }

    void setup_timeline(void) {
      const vec<unsigned int>& est_ord(by_est.get());
      const vec<unsigned int>& lct_ord(by_lct.get());
      // std::sort(est_ord.begin(), est_ord.end(),
      //   [&](int u, int v) { return est(u) < est(v); });
      // std::sort(lct_ord.begin(), lct_ord.end(),
      //   [&](int u, int v) { return ldct(u) < ldct(v); });
      
      assert(ub(cap) > 0);
      int _slack = 1 + eMax/ub(cap);

      int b(est(est_ord[0]));
      bounds[0] = b-_slack; // FIXME
      bounds[1] = b;
      nb = 1;
      unsigned int* u_it(lct_ord.begin());
      int u_b(ldct(*u_it));

      for(unsigned int ii : est_ord) {
        int l_i(est(ii));
        // Process any upper bounds which are _strictly_ below the next lb.
        while(u_b < l_i) {
          if(b < u_b) {
            ++nb;
            bounds[nb] = b = u_b;
          }
          maxrank[*u_it] = nb;
          ++u_it;
          u_b = ldct(*u_it);
        }
        // And now do the lb.
        if(b < l_i) {
          ++nb;
          bounds[nb] = b = l_i;
        }
        minrank[ii] = nb;
      }
      // Now process the remaining upper bounds.
      for(; u_it != lct_ord.end(); ++u_it) {
        u_b = ldct(*u_it);
        if(b < u_b) {
          ++nb;
          bounds[nb] = b = u_b;
        }
        maxrank[*u_it] = nb;
      }
      bounds[nb+1] = u_b+_slack;
    }

    bool check_overload(vec<clause_elt>& confl) {
      V cMax(ub(cap));
      // Initialize the timeline
      for(int i = 1; i <= nb+1; i++) {
        t[i] = h[i] = i-1;  
        d[i] = cMax * (bounds[i] - bounds[i-1]);
      }

      // Order tasks by ub(t.s) + lb(t.d).
      const vec<unsigned int>& lct_ord(by_lct.get());
      for(int u : lct_ord) {
        // Try scheduling the task.  
        V e(mdur(u) * mreq(u));
        int x = minrank[u];
        int y = maxrank[u];
        int z = pathmax(t, x+1);
        int j = t[z];

        while(d[z] <= e) {
          e -= d[z];
          d[z] = 0;
          t[z] = z+1;
          z = pathmax(t, t[z]);
          t[z] = j;
        }
        d[z] -= e;        
        pathset(t, x+1, z, z);
        if(d[z] < cMax * (bounds[z] - bounds[y])) {
          // ex_env(bounds[t[z]], bounds[y], confl);
          ex_env_l(bounds[y], confl);
          // fprintf(stderr, "%% Overload!\n");
          return false;
        }
      }
      return true;
    }

    watch_result wake(int t) {
      queue_prop();
      return Wt_Keep;
    }
  public:
    cumul_TL(solver_data* s, vec<intvar>& starts, vec<intvar>& dur, vec<R>& res, R _cap)
      : propagator(s), cap(_cap)
      , by_est(s)
      , by_lct(s)
      , bounds(new int[2 * starts.size() + 2])
      , d(new int[2 * starts.size() + 2])
      , t(new int[2 * starts.size() + 2])
      , h(new int[2 * starts.size() + 2])
      , minrank(new int[starts.size()])
      , maxrank(new int[starts.size()])
      , eMax(0)
      {
      int rMax(ub(cap));

      for(int xi : irange(starts.size())) {
        // Skip any tasks which are definitely irrelevant.
        if(!ub(dur[xi]) || !ub(res[xi]))
          continue;
        if(lb(res[xi]) > rMax)
          throw RootFail();
        eMax += ub(dur[xi]) * ub(res[xi]);

        task_info t(task_info { starts[xi], dur[xi], res[xi] });
        tasks.push(t);
      }
      for(int xi: irange(tasks.size())) {
        task_info& t(tasks[xi]);
        t.s.attach(E_LB, this->template watch<&P::wake>(xi));
        t.s.attach(E_UB, this->template watch<&P::wake>(xi));

        t.d.attach(E_LB, this->template watch<&P::wake>(xi));
        t.r.attach(s, E_LB, this->template watch<&P::wake>(xi));
        // est_ord.push(xi);
        // lct_ord.push(xi);
        by_est.add(t.s);
        by_lct.add(t);
      }
      cap.attach(s, E_UB, this->template watch<&P::wake>(0));
    }

    bool propagate(vec<clause_elt>& confl) {
      // fprintf(stderr, "Active: %d of %d\n", active_tasks.size(), tasks.size());
      setup_timeline();
      return check_overload(confl);
    }

    ~cumul_TL(void) {
      delete[] bounds;
      delete[] d;
      delete[] h;
      delete[] minrank;
      delete[] maxrank;
    }

    void cleanup(void) {
      is_queued = false;
    }
  };
};

bool cumulative(solver_data* s,
  vec<intvar>& starts, vec<int>& duration, vec<int>& resource, int cap) {
  // new cumul_prop(s, starts, duration, resource, cap);
  // return true;
  return cumul<int>::cumul_val::post(s, starts, duration, resource, cap);
}

bool cumulative_var(solver_data* s,
  vec<intvar>& starts, vec<intvar>& duration, vec<intvar>& resource, intvar cap) {
  // new cumul_prop(s, starts, duration, resource, cap);
  // return true;
//   return cumul<int>::cumul_var<intvar>::post(s, starts, duration, resource, cap)
  return cumul<int>::cumul_var_lw<intvar>::post(s, starts, duration, resource, cap)
    && cumul<int>::cumul_TL<intvar>::post(s, starts, duration, resource, cap)
    ;
}


bool cumulative_float(solver_data* s,
  vec<intvar>& starts, vec<int>& duration, vec<float>& resource, float cap) {
  // new cumul_prop(s, starts, duration, resource, cap);
  // return true;
  return cumul<float>::cumul_val::post(s, starts, duration, resource, cap);
}

struct sel_resource {
  sel_resource(int _r, patom_t _active)
    : r(_r), active(_active) { }

  typedef int val_t;

  int lb(const ctx_t& ctx) const { return active.lb(ctx) ? r : 0; } 
  int ub(const ctx_t& ctx) const { return active.ub(ctx) ? r : 0; }
  int lb(const solver_data* s) const { return lb(s->ctx()); }
  int ub(const solver_data* s) const { return ub(s->ctx()); }
  int model_val(const model& m) const { return m.value(active) ? r : 0; }

  patom_t operator>=(val_t v) const {
    if(v <= 0) return at_True;
    if(v <= r) return active;
    return at_False;
  }
  patom_t operator<=(val_t v) const {
    if(v < 0) return at_False;
    if(v < r) return ~active;
    return at_True;
  }
  patom_t operator>(val_t v) const { return (*this) >= v+1; }
  patom_t operator<(val_t v) const { return (*this) <= v-1; }
  patom_t operator==(val_t v) const {
    if(v == 0) return ~active;
    if(v == r) return active;
    return at_False;
  }
  void attach(solver_data* s, intvar_event e, watch_callback c) {
    if(e&(E_LB | E_FIX)) {
      geas::attach(s, active, c);
    }
    if(e&(E_UB | E_FIX)) {
      geas::attach(s, ~active, c);
    }
  }

  // TODO: Think about boundary conditions
  int lb_of_pval(pval_t p) const {
    if(p > pval_max)
      return r+1;
    return p >= active.val ? r : 0;
  }
  int ub_of_pval(pval_t p) const { return pval_inv(p) < active.val ? 0 : r; }

  int r;
  patom_t active;
};

bool cumulative_sel(solver_data* s,
  vec<intvar>& starts, vec<intvar>& duration, vec<int>& resource, vec<patom_t>& sel, int cap) {
  /* */
  vec<sel_resource> rsel;
  for(int ii : irange(resource.size()))
    rsel.push(sel_resource(resource[ii], sel[ii]));
  return cumul<int>::cumul_var_lw<sel_resource>::post(s, starts, duration, rsel, sel_resource(cap, at_True))
    && cumul<int>::cumul_TL<sel_resource>::post(s, starts, duration, rsel, sel_resource(cap, at_True))
    ;
    /* /
    vec<intvar> rvars;
    for(int ii : irange(resource.size())) {
      intvar r(new_intvar(s, 0, resource[ii]));
      vec<int> vals;
      vals.push(0);
      vals.push(resource[ii]);
      add_clause(s, ~sel[ii], r >= resource[ii]);
      rvars.push(r);
    }
    intvar cvar(new_intvar(s, cap, cap));
    return cumul<int>::cumul_var_lw<intvar>::post(s, starts, duration, rvars, cvar)
      && cumul<int>::cumul_TL<intvar>::post(s, starts, duration, rvars, cvar)
      ;
    /  */
}


}
