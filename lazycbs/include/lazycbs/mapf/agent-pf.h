#ifndef GEAS_AGENT__PF_H
#define GEAS_AGENT__PF_H
#include <utility>
#include <functional>
#include "single_agent_ecbs.h"

#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/vars/intvar.h>

#include <geas/mtl/bool-set.h>

#define MAPF_BETTER_EXPLANATIONS
namespace mapf {

using namespace geas;

class Agent_PF : public propagator, public prop_inst<Agent_PF> {
  // An obstacle, with the activating atom.
  enum ObstacleType { O_MUTEX, O_BARRIER };
  struct barrier_info {
    int pos; // Barrier position at the start time
    int delta; // Difference between successive barrier positions
    int duration; // How long does the barrier hold?
  };
  struct obstacle_info {
    obstacle_info(patom_t _at, int _timestep, std::pair<int, int> _p)
      : at(_at), timestep(_timestep), tag(O_MUTEX), p(_p) { }
    obstacle_info(patom_t _at, int _timestep, int loc, int delta, int duration)
      : at(_at), timestep(_timestep), tag(O_BARRIER), b({ loc, delta, duration}) { }
    patom_t at;
    int timestep;
    ObstacleType tag;
    
    union { 
      barrier_info b;
      std::pair<int, int> p;
    };
  };

  // A (previous) incumbent.
  struct path_info {
    double cost;
    vec<int> path;
  };

  // In both cases, only wake up if the new obstacle would invalidate
  // the incumbent.
  watch_result wake_cost(int _xi) {
    // Only wake up if the incumbent is invalidated.
    if(ub(cost) < history[hist_pos].cost) {
      queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_obstacle(int ci) {
    apply_obstacle(ci);
    if(incumbent_conflicts_with(ci)) {
      queue_prop();
    }
    return Wt_Keep;
  }

  void expl_length(int tl, pval_t p, vec<clause_elt>& expl) {
    // For now, just collect the set of constraints that were active.
#ifndef MAPF_BETTER_EXPLANATIONS
    obstacle_atoms(tl, expl);
#else
    vec<int> ex_csts;
    extract_lb_explanation(tl, cost.lb_of_pval(p), ex_csts);
    for(int c : ex_csts)
      EX_PUSH(expl, ~obstacles[c].at);
#endif
  }

  void obstacle_atoms(int tl, vec<clause_elt>& expl) {
    for(int si = 0; si < tl; ++si) {
      EX_PUSH(expl, ~obstacles[obs_stack[si]].at);
    }
  }

  // Restore the active constraints to the state we _should_ be in now,
  // looking at obs_tl.
  void revert_barrier(int t, const barrier_info& b) {
#if 0
    int end = t + b.duration;
    for(; t < end; ++t)
      active_obstacles[t].pop_back();
#else
    int p = b.pos;
    int end = t + b.duration;
    for(; t < end; ++t) {
      active_obstacles[p].pop_back(); 
      p += b.delta;
    }
#endif
  }

  void restore_stack(void) {
    // Iteration order doesn't matter, because the multiset of pops
    // is the same.
    for(int si = obs_tl; si < obs_stack.size(); ++si) {
      const obstacle_info& o(obstacles[obs_stack[si]]);
      if(o.tag == O_BARRIER) {
        revert_barrier(o.timestep, o.b);
      } else {
#if 0
        active_obstacles[o.timestep].pop_back();
        if(o.p.second >= 0)
          active_obstacles[o.timestep].pop_back();
#else
        active_obstacles[o.p.first].pop_back();
        if(o.p.second >= 0)
          active_obstacles[o.p.second].pop_back();
#endif
      }
    }
    obs_stack.shrink(obs_stack.size() - obs_tl);
  }

  void apply_barrier(int t, const barrier_info& b) {
    int p = b.pos;
    int end = t + b.duration;
    for(; t < end; ++t) {
#if 0
      active_obstacles[t].push_back(std::make_pair(p, -1));
#else
      active_obstacles[p].push_back(std::make_pair(t, -1));
#endif
      p += b.delta;
    }
  }
  void apply_obstacle(int ci) {
    // Make sure we're starting from a consistent state.
    if(obs_tl < obs_stack.size())
      restore_stack();
    
    // Then apply the new obstacle.
    const obstacle_info& o(obstacles[ci]);
#if 0
    int tMax = (o.tag == O_BARRIER) ? o.timestep + o.b.duration : o.timestep+1;
    while((int) active_obstacles.size() < tMax)
      active_obstacles.push_back(std::list<std::pair<int, int>>());
#endif

    obs_stack.push(ci);
    set(obs_tl, obs_stack.size());
    if(o.tag == O_BARRIER) {
      apply_barrier(o.timestep, o.b);
    } else {
#if 0
      active_obstacles[o.timestep].push_back(o.p);
      if(o.p.second >= 0)
        active_obstacles[o.timestep].push_back(std::make_pair(o.p.second, o.p.first));
#else
      if(o.p.second >= 0) {
        active_obstacles[o.p.first].push_back(std::make_pair(o.timestep+1, o.p.second));
        active_obstacles[o.p.second].push_back(std::make_pair(o.timestep+1, o.p.first));
      } else {
        active_obstacles[o.p.first].push_back(std::make_pair(o.timestep, -1));
      }
#endif
    }
  }

  bool incumbent_conflicts_with(int ci) {
    const obstacle_info& o(obstacles[ci]);
    const vec<int>& path(history[hist_pos].path);
    if(o.tag == O_BARRIER) {
      int p = o.b.pos;
      for(int t = o.timestep; t < o.timestep + o.b.duration; ++t) {
        int ap = (t < path.size()) ? path[t] : path.last();
        if(ap == p)
          return true;
        p += o.b.delta;
      }
      return false;
    } else {
      if(o.p.second == -1) {
        return (o.timestep < path.size()) ?  path[o.timestep] == o.p.first : path.last() == o.p.first;
      } else {
        // FIXME: Should make edge conflicts bidirectional.
        if(o.timestep + 1 < (int) path.size()) {
          if(path[o.timestep] == o.p.first && path[o.timestep+1] == o.p.second)
            return true;
          if(path[o.timestep] == o.p.second && path[o.timestep+1] == o.p.first)
            return true;
        }
        return false;
      }
    }
  }

  void update_incumbent(void) {
    const std::vector<int>& path(engine.path);
    if(history[hist_pos].cost < engine.path_cost) {
      // Incumbent got strictly worse. Make sure the old one
      // will get restored on backtracking.
      set(hist_pos, hist_pos+1);
      if(hist_pos == history.size())
        history.push();
      history[hist_pos].cost = engine.path_cost;
    }

    // Now copy the new path over the old incumbent
    history[hist_pos].path.clear();
    for(int p : path)
      history[hist_pos].path.push(p);  
  }

public:
  Agent_PF(solver_data* s, intvar _cost, int start_location, int goal_location, const double* heuristic, const bool* map, int map_size, const int* actions_offset,
    std::function<std::pair<int, bool*>() > _get_reservations)
    : propagator(s), engine(start_location, goal_location, heuristic, map, map_size, actions_offset), get_reservations(_get_reservations)
    , active_obstacles(map_size)
    , start_pos(start_location), goal_pos(goal_location)
    , cost(_cost), obs_tl(0), hist_pos(0)
    , has_bypass(false)
#ifdef MAPF_BETTER_EXPLANATIONS
    // Initialize support structures for explanation
    , start_dist(map_size, DBL_MAX)
    , has_blocked(map_size)
    , has_forbidden(map_size)
    , block_idx(map_size, 0)
    , is_queued(map_size)
    , forbidden_pred(map_size)
#endif
    , num_expanded(0), num_generated(0), num_executions(0)
    {
    cost.attach(E_UB, watch<&P::wake_cost>(0, Wt_IDEM));
    auto res(get_reservations());
    num_executions++;
    if(!engine.findPath(1.0, &active_obstacles, res.second, res.first))
      throw RootFail();
    num_generated += engine.num_generated;
    num_expanded += engine.num_expanded;

    if(cost.lb(s) < engine.path_cost) {
      if(!set_lb(cost, engine.path_cost, reason()))
        throw RootFail();
    }

    history.push();
    history[0].cost = engine.path_cost;   
    update_incumbent();

#ifdef MAPF_BETTER_EXPLANATIONS
    for(int ii = 0; ii < map_size; ++ii) {
      blocked_times.push();
      forbidden_times.push();
    }

    // Initialize the reverse heuristic. Because distances are uniform, we just use a queue.
    is_queued.add(start_pos);
    pred.push(start_pos);
    start_dist[start_pos] = 0.0;
    for(int qi = 0; qi < pred.size(); ++qi) {
      int l(pred[qi]);
      double d_adj = start_dist[l] + 1;
      for(int d : engine.directions) {
        int adj(l + engine.actions_offset[d]);
        if(!engine.my_map[adj] && !is_queued.elem(adj)) {
          start_dist[adj] = d_adj;
          is_queued.add(adj);
          pred.push(adj);
        }
      }
    }
    pred.clear();
    is_queued.clear();
#endif
  }

  bool check_sat(ctx_t& ctx);
  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); };

  int register_obstacle(patom_t at, int timestep, int l1, int l2) {
    int ci(obstacles.size()); 
    // Add the new constraint to the pool
    obstacles.push(obstacle_info(at, timestep, std::make_pair(l1,l2)));
    // And make sure the propagator wakes up when becomes set.
    attach(s, at, watch<&P::wake_obstacle>(ci, Wt_IDEM));
    return ci;
  }

  int register_barrier(patom_t at, int timestep, int loc, int delta, int duration) {
    int ci(obstacles.size()); 
    // Add the new constraint to the pool
    obstacles.push(obstacle_info(at, timestep, loc, delta, duration));
    // And make sure the propagator wakes up when becomes set.
    attach(s, at, watch<&P::wake_obstacle>(ci, Wt_IDEM));
    return ci;
  }

  bool propagate(vec<clause_elt>& confl) {
    has_bypass = 0;
    assert(obs_stack.size() == obs_tl);
    auto res(get_reservations());
    num_executions++;
    if(!engine.findPath(1.0, &active_obstacles, res.second, res.first)) {
      num_generated += engine.num_generated;
      num_expanded += engine.num_expanded;

      // Failed to produce any path
      obstacle_atoms(obs_stack.size(), confl);
      return false;
    }
    num_generated += engine.num_generated;
    num_expanded += engine.num_expanded;

    // Otherwise, update the lower bound.
    int p_cost = std::ceil(engine.path_cost);
    if(lb(cost) < p_cost) {
      if(!set_lb(cost, p_cost, expl<&P::expl_length>(obs_stack.size())))
        return false;
    }
    update_incumbent();
    return true;
  }

  bool find_bypass(void) {
    auto res(get_reservations());
    num_executions++;
    // if(engine.findPath_upto(ub(cost), &active_obstacles, res.second, res.first)) {
    if(engine.findPath_upto(ub(cost), &active_obstacles, res.second, res.first)) {
      // Make sure the bypass is reset after backtracking
      if(!has_bypass)
        s->persist.bt_flags.push(&has_bypass);
      has_bypass = true; 
    
      const std::vector<int>& path(engine.path);
      bypass_path.clear();
      for(int p : path)
        bypass_path.push(p);
      return true;
    }
    return false;
  }

  const vec<int>& getPath(void) const { return has_bypass ? bypass_path : history[hist_pos].path; }
  void extractPath(vec<int>& path) const {
    if(has_bypass)
      bypass_path.copyTo(path);
    else
      history[hist_pos].path.copyTo(path);
  }
  double pathCost(void) const { return has_bypass ? bypass_path.size()-1 : history[hist_pos].cost; }

  // The search engine
  SingleAgentECBS engine;
  std::function<std::pair<int, bool*>()> get_reservations;

  // Set of obstacles, as the engine expects to find them
  // std::vector< std::list<std::pair<int, int> > > active_obstacles;
  std::vector< std::vector<std::pair<int, int> > > active_obstacles;

  int start_pos;
  int goal_pos;

  intvar cost;

  vec<obstacle_info> obstacles; // The registered obstacles
  vec<int> obs_stack;           // The history of pushed obstacles
  Tint obs_tl;                  // How big _should_ obs_stack be?

  vec<path_info> history; // The history of previous incumbents
  Tint hist_pos;          // Which is our current incumbent?

  vec<int> bypass_path;
  char has_bypass;

#ifdef MAPF_BETTER_EXPLANATIONS
  // Retrofitting to generate explanations
  void extract_lb_explanation(unsigned int obs_tl, unsigned int lb, vec<int>& ex_csts);
  vec<double> start_dist; // Minimum distance from the start location.

  // For each location, at what times is it marked as 'forbidden'?
  struct blockage_info {
    int pred;
    int t;
    int cst; 
  };

  boolset has_blocked;
  boolset has_forbidden;
  vec< vec<blockage_info> > blocked_times;
  vec< vec<blockage_info> > forbidden_times;
  vec<int> block_idx;

  // For iterating in time order.
  boolset is_queued;
  vec<int> curr;
  vec<int> pred;

  boolset forbidden_pred;
#endif
  // Tracking statistics
  int num_expanded;
  int num_generated;
  int num_executions;
};

}
#endif
