#include <lazycbs/mapf/agent-pf.h>
// #define EXPLAIN_LATEST

namespace mapf {
#ifdef MAPF_BETTER_EXPLANATIONS
void prune_blockages(vec<Agent_PF::blockage_info>& b) {
  Agent_PF::blockage_info* s(b.begin());
  Agent_PF::blockage_info* e(b.end());
  Agent_PF::blockage_info* c(b.begin());

  while(s != e) {
    // Process all blockages at t in a chunk.
    int t = s->t;
    // Find the end of this time range.
    Agent_PF::blockage_info* te(s);
    for(; te != e; ++te) {
      if(te->t != t)
        break;
    }
    if(s->pred < 0) {
      // Vertex conflict. Keep only one; edge conflicts are irrelevant.
      *c = *s;
      ++c;
      s = te;
    } else {
      // Edge conflict. In this case, keep everything. Shouldn't have
      // any duplicates, because edge conflicts are unique.
      for(; s != te; ++s, ++c)
        *c = *s;
    }
  }
  // Now cut b down to the new size.
  b.shrink(e - c);  
}

#ifdef EXPLAIN_LATEST
void Agent_PF::extract_lb_explanation(unsigned int obs_tl, unsigned int lb, vec<int>& ex_csts) {
  for(unsigned int ii = 0; ii < obs_tl; ++ii) {
    int ci(obs_stack[ii]);
    const obstacle_info& o(obstacles[ci]);

     // Then apply the new obstacle.
    // int tMax = (o.tag == O_BARRIER) ? o.timestep + o.b.duration : o.timestep+1;

    if(o.tag == O_BARRIER) {
      const barrier_info& b(o.b);
      int t = o.timestep;
      int p = b.pos;
      int end = t + b.duration;
      for(; t < end; ++t) {
        if(!has_blocked.elem(p))
          has_blocked.add(p);
        blocked_times[p].push(blockage_info { -1, t, ci });
        if(p == goal_pos)
          lb = std::max(lb, (unsigned int) t+1);
        p += b.delta;
      }
    } else {
      if(!has_blocked.elem(o.p.first))
        has_blocked.add(o.p.first);
      if(o.p.second < 0) {
        // Vertex constraint
        blocked_times[o.p.first].push(blockage_info { -1, o.timestep, ci });
        if(o.p.first == goal_pos)
          lb = std::max(lb, (unsigned int) o.timestep+1);
      } else {
        if(!has_blocked.elem(o.p.second))
          has_blocked.add(o.p.second);
        // Edge constraint
        blocked_times[o.p.first].push(blockage_info { o.p.second, o.timestep+1, ci });
        blocked_times[o.p.second].push(blockage_info { o.p.first, o.timestep+1, ci });
      }
    }
  }
  // We'll be walking backwards, so order the obstacles by descending time.
  for(unsigned int l : has_blocked) {
    block_idx[l] = 0;
    vec<blockage_info>& b(blocked_times[l]);
    std::sort(b.begin(), b.end(),
      [this](const blockage_info& u, const blockage_info& v) {
        if(u.t != v.t)
          return u.t > v.t;
        // Prefer vertex conflicts
        if(u.pred != v.pred)
          return u.pred < v.pred;
        // Within vertex conflicts, prefer more recent barriers
        if(obstacles[u.cst].timestep != obstacles[v.cst].timestep)
          return obstacles[u.cst].timestep < obstacles[v.cst].timestep;
        // Otherwise, prefer barriers which finish later
        return obstacles[u.cst].timestep + obstacles[u.cst].b.duration >
          obstacles[v.cst].timestep + obstacles[v.cst].b.duration; });
    // Now throw away obstacles which won't be relevant.
    prune_blockages(b);
  }

  // Starting from the goal, walk backwards. 
  int t(lb);
  is_queued.add(goal_pos);
  pred.push(goal_pos);

  while(pred.size() > 0) {
    --t;
    is_queued.clear();
    curr.clear();
    std::swap(pred, curr);
    
    for(int l : curr) {
      // Check the heuristic cutoff.
      if(t < start_dist[l])
        continue;
       
      // Adjust block_idx.
      int b_idx(block_idx[l]);
      vec<blockage_info>& bs(blocked_times[l]);
      while(b_idx < bs.size() && bs[b_idx].t > t)
        b_idx++;
      if(b_idx < bs.size() && bs[b_idx].t == t) {
        // Some blockage is active at this time.
        if(bs[b_idx].pred == -1) {
          // Vertex is forbidden.
          if(!has_forbidden.elem(l))
            has_forbidden.add(l);
          forbidden_times[l].push(blockage_info{ -1, t, bs[b_idx].cst });
          block_idx[l] = b_idx;
          continue;
        } else {
          // Some edges are forbidden
          for(; b_idx < bs.size() && bs[b_idx].t == t; ++b_idx) {
            unsigned int p(bs[b_idx].pred);
            if(!has_forbidden.elem(p))
              has_forbidden.add(p);
            forbidden_pred.add(p);
            forbidden_times[p].push(blockage_info { l, t-1, bs[b_idx].cst });
          }
        }
      }
      block_idx[l] = b_idx;

      // Now mark any predecessors which haven't been forbidden.
      for(int d : engine.directions) {
        int p(l + engine.actions_offset[d]);
        if(!engine.my_map[p] && !forbidden_pred.elem(p) && !is_queued.elem(p)) {
          is_queued.add(p);
          pred.push(p);
        }
      }
      forbidden_pred.clear();
    }
  }
  // Now reset the blockages.
  for(int l : has_blocked) {
    block_idx[l] = 0;
    blocked_times[l].clear();
  }
  has_blocked.clear();
  
  // Now work forward from the start.
  t = 0;
  is_queued.add(start_pos);
  curr.push(start_pos);

  // We're now exploring forward in time, so reverse the obstacles.
  for(unsigned int l : has_forbidden) {
    std::sort(forbidden_times[l].begin(), forbidden_times[l].end(),
      [](const blockage_info& u, const blockage_info& v) {
        if(u.t != v.t)
          return u.t < v.t;
        return u.pred < v.pred;
      });
  }

  while(curr.size() > 0) {
    pred.clear();
    is_queued.clear();
    std::swap(pred, curr);
    for(unsigned int l : pred) {
      // Cut off any locations which are too far.
      if(t + engine.my_heuristic[l] >= lb)
        continue;
      // TODO: For barriers, check if the barrier is already active.
      // Check if anything is forbidden here at time t.
      vec<blockage_info>& bs(forbidden_times[l]);
      int b_idx(block_idx[l]);
      while(b_idx < bs.size() && bs[b_idx].t < t)
        ++b_idx;
      if(b_idx < bs.size() && bs[b_idx].t == t) {
        // Something is forbidden.
        if(bs[b_idx].pred == -1) {
          // Vertex conflict.
          ex_csts.push(bs[b_idx].cst);               
          block_idx[l] = b_idx;
          continue;
        } else {
          // Edge conflicts
          for(; b_idx < bs.size() && bs[b_idx].t == t; ++b_idx) {
            forbidden_pred.add(bs[b_idx].pred);
            ex_csts.push(bs[b_idx].cst);
          }
          block_idx[l] = b_idx;
        }
      }
      // Now expand neighbours.
      for(int d : engine.directions) {
        unsigned int s(l + engine.actions_offset[d]);
        if(!engine.my_map[s] && !forbidden_pred.elem(s) && !is_queued.elem(s)) {
          curr.push(s);
          is_queued.add(s);
        }
      }
      forbidden_pred.clear();
    }
    ++t;
  }
  // Now cleanup
  for(unsigned int l : has_forbidden) {
    block_idx[l] = 0;
    forbidden_times[l].clear();
  }
  has_forbidden.clear();
}
#else
// Get the earliest explanation
void Agent_PF::extract_lb_explanation(unsigned int obs_tl, unsigned int lb, vec<int>& ex_csts) {
  for(unsigned int ii = 0; ii < obs_tl; ++ii) {
    int ci(obs_stack[ii]);
    const obstacle_info& o(obstacles[ci]);

     // Then apply the new obstacle.
    // int tMax = (o.tag == O_BARRIER) ? o.timestep + o.b.duration : o.timestep+1;

    if(o.tag == O_BARRIER) {
      const barrier_info& b(o.b);
      int t = o.timestep;
      int p = b.pos;
      int end = t + b.duration;
      for(; t < end; ++t) {
        if(!has_blocked.elem(p))
          has_blocked.add(p);
        blocked_times[p].push(blockage_info { -1, t, ci });
        if(p == goal_pos)
          lb = std::max(lb, (unsigned int) t+1);
        p += b.delta;
      }
    } else {
      if(!has_blocked.elem(o.p.first))
        has_blocked.add(o.p.first);
      if(o.p.second < 0) {
        // Vertex constraint
        blocked_times[o.p.first].push(blockage_info { -1, o.timestep, ci });
        if(o.p.first == goal_pos)
          lb = std::max(lb, (unsigned int) o.timestep+1);
      } else {
        if(!has_blocked.elem(o.p.second))
          has_blocked.add(o.p.second);
        // Edge constraint
        blocked_times[o.p.first].push(blockage_info { o.p.second, o.timestep, ci });
        blocked_times[o.p.second].push(blockage_info { o.p.first, o.timestep, ci });
      }
    }
  }
  // Initially walking forwards, so order by increasing time.
  for(unsigned int l : has_blocked) {
    block_idx[l] = 0;
    vec<blockage_info>& b(blocked_times[l]);
    std::sort(b.begin(), b.end(),
      [this](const blockage_info& u, const blockage_info& v) {
        if(u.t != v.t)
          return u.t < v.t;
        // Prefer vertex conflicts
        if(u.pred != v.pred)
          return u.pred < v.pred;
        // Within vertex conflicts, prefer more recent barriers
        if(obstacles[u.cst].timestep != obstacles[v.cst].timestep)
          return obstacles[u.cst].timestep < obstacles[v.cst].timestep;
        // Otherwise, prefer barriers which finish later
        return obstacles[u.cst].timestep + obstacles[u.cst].b.duration >
          obstacles[v.cst].timestep + obstacles[v.cst].b.duration; });
    // Now throw away obstacles which won't be relevant.
    prune_blockages(b);
  }

  // Starting from the start, walk forwards.
  int t(0);
  is_queued.add(start_pos);
  curr.push(start_pos);

  while(curr.size() > 0) {
    is_queued.clear();
    pred.clear();
    std::swap(curr, pred);
    
    for(int l : pred) {
      // Check the heuristic cutoff.
      if(t + engine.my_heuristic[l] >= lb)
        continue;
       
      // Adjust block_idx.
      int b_idx(block_idx[l]);
      vec<blockage_info>& bs(blocked_times[l]);
      while(b_idx < bs.size() && bs[b_idx].t < t)
        b_idx++;
      if(b_idx < bs.size() && bs[b_idx].t == t) {
        // Some blockage is active at this time.
        if(bs[b_idx].pred == -1) {
          // Vertex is forbidden.
          if(!has_forbidden.elem(l))
            has_forbidden.add(l);
          forbidden_times[l].push(blockage_info{ -1, t, bs[b_idx].cst });
          block_idx[l] = b_idx;
          continue;
        } else {
          // Some edges are forbidden
          for(; b_idx < bs.size() && bs[b_idx].t == t; ++b_idx) {
            unsigned int p(bs[b_idx].pred);
            if(!has_forbidden.elem(p))
              has_forbidden.add(p);
            forbidden_pred.add(p);
            forbidden_times[p].push(blockage_info { l, t+1, bs[b_idx].cst });
          }
        }
      }
      block_idx[l] = b_idx;

      // Now mark any predecessors which haven't been forbidden.
      for(int d : engine.directions) {
        int p(l + engine.actions_offset[d]);
        if(!engine.my_map[p] && !forbidden_pred.elem(p) && !is_queued.elem(p)) {
          is_queued.add(p);
          curr.push(p);
        }
      }
      forbidden_pred.clear();
    }
    ++t;
  }
  // Now reset the blockages.
  for(int l : has_blocked) {
    block_idx[l] = 0;
    blocked_times[l].clear();
  }
  has_blocked.clear();
  
  // Now work forward from the start.
  t = lb-1;
  is_queued.add(goal_pos);
  pred.push(goal_pos);

  // We're now exploring backward in time, so reverse the obstacles.
  for(unsigned int l : has_forbidden) {
    std::sort(forbidden_times[l].begin(), forbidden_times[l].end(),
      [](const blockage_info& u, const blockage_info& v) {
        if(u.t != v.t)
          return u.t > v.t;
        return u.pred < v.pred;
      });
  }

  while(pred.size() > 0) {
    curr.clear();
    is_queued.clear();
    std::swap(curr, pred);
    for(unsigned int l : curr) {
      // Cut off any locations which are too far.
      if(t < start_dist[l])
        continue;
      // TODO: For barriers, check if the barrier is already active.
      // Check if anything is forbidden here at time t.
      vec<blockage_info>& bs(forbidden_times[l]);
      int b_idx(block_idx[l]);
      while(b_idx < bs.size() && bs[b_idx].t > t)
        ++b_idx;
      if(b_idx < bs.size() && bs[b_idx].t == t) {
        // Something is forbidden.
        if(bs[b_idx].pred == -1) {
          // Vertex conflict.
          ex_csts.push(bs[b_idx].cst);               
          block_idx[l] = b_idx;
          continue;
        } else {
          // Edge conflicts
          for(; b_idx < bs.size() && bs[b_idx].t == t; ++b_idx) {
            forbidden_pred.add(bs[b_idx].pred);
            ex_csts.push(bs[b_idx].cst);
          }
          block_idx[l] = b_idx;
        }
      }
      // Now expand neighbours.
      for(int d : engine.directions) {
        unsigned int s(l + engine.actions_offset[d]);
        if(!engine.my_map[s] && !forbidden_pred.elem(s) && !is_queued.elem(s)) {
          pred.push(s);
          is_queued.add(s);
        }
      }
      forbidden_pred.clear();
    }
    --t;
  }
  // Now cleanup
  for(unsigned int l : has_forbidden) {
    block_idx[l] = 0;
    forbidden_times[l].clear();
  }
  has_forbidden.clear();
}
#endif

bool Agent_PF::check_sat(ctx_t& ctx) {
  return true;
#if 0
  std::vector< std::vector<std::pair<int, int> > > local_obstacles;
  // Walk through all the obstacles, and activate any that are present.
  int cap(cost.ub(ctx));
  for(int ii = 0; ii <= cap; ++ii)
    local_obstacles.push_back(std::list<std::pair<int, int> >());

  for(const obstacle_info& o : obstacles) {
    int t(o.timestep);
    if(o.at.lb(ctx)) {
      // Activated 
      if(o.tag == O_BARRIER) {
        const barrier_info& b(o.b);
        int p = b.pos;
        int end = std::min(cap + 1, t + b.duration);
        for(; t < end; ++t) {
          local_obstacles[t].push_back(std::make_pair(p, -1));
          p += b.delta;
        }
      } else {
        // Mutex. First check if we're blocking the goal.
        if(o.p.first == goal_pos && o.p.second == -1 && cap <= t)
          return false;

        // Otherwise, skip anything later than cap.
        if(cap <= t)
          continue;
        local_obstacles[t].push_back(o.p);
        if(o.p.second >= 0)
          local_obstacles[t].push_back(std::make_pair(o.p.second, o.p.first));
      }
    }
  }
  if(!engine.findPath(1.0, &local_obstacles, nullptr, 0))
    return false;

  int p_cost = std::ceil(engine.path_cost);
  return p_cost <= cap;
#endif
}

#endif

}
