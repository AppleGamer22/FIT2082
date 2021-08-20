// Propagator for bipartite matching-based constraints.
// So, all-different, gcc, inverse, ...
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/vars/intvar.h>
#include <geas/utils/interval.h>
#include <geas/mtl/bool-set.h>

#include <geas/constraints/flow/flow.h>

// #define LOG_FLOW
namespace geas {

class bp_flow_int : public propagator, public prop_inst<bp_flow_int> {
  watch_result wake_kill(int fi) {
    if(used_flow[fi]) {
      dead_flows.push(fi);
      queue_prop();
    }
    return Wt_Keep;
  }
  watch_result wake_fix(int fi) {
    if(!used_flow[fi]) {
      fixed_flows.push(fi);
      queue_prop();
    }
    return Wt_Keep;
  }
  
  void ex_pos(int fi, pval_t _p, vec<clause_elt>& expl) {
#ifdef LOG_FLOW
    fprintf(stderr, "Explain: [%d -> %d]\n", flows[fi].src, flows[fi].sink);
    log_state();
#endif
    bflow& f(flows[fi]);
    bool r = mark_reach<true>(f.src, f.sink, fi);
    assert(!r);
    make_expl<true>(fi, f.src, f.sink, expl);
  }

  void ex_neg(int fi, pval_t _p, vec<clause_elt>& expl) {
#ifdef LOG_FLOW
    fprintf(stderr, "Explain: ~ [%d -> %d]\n", flows[fi].src, flows[fi].sink);
    log_state();
#endif
    bflow& f(flows[fi]);
    bool r = mark_reach<false>(f.src, f.sink, fi);
    assert(!r);
    make_expl<false>(fi, f.src, f.sink, expl);
  }

  void log_state(void) {
    fprintf(stderr, "[[%d, %d]]\n", out_flows.size(), in_flows.size());
    for(int ii : irange(out_flows.size())) {
      fprintf(stderr, "%d:", ii);  
      for(int fi : out_flows[ii]) {
        fprintf(stderr, " {%d : %s | %s}",
          flows[fi].sink,
          used_flow[fi] ? "+" : "_",
          lb(flows[fi].at) ? "T" :
            !ub(flows[fi].at) ? "F" : "?");
      }
      fprintf(stderr, " (%d)\n", sccs[ii]);
    }
  }

  // Explanation is two-phase: mark reachability, then
  // sweep backwards collecting the necessary atoms.
  // S = true: failed to add a path between si and di.
  // S = false: failed to remove a path between si and di.
  template<int S>
  void make_expl(int f_ex, int si, int di, vec<clause_elt>& expl) {
    // Assumes  mark_reach has already been called, and 
    // src_seen/sink_seen are up to date.
#if 0
    for(int fi : irange(flows.size())) {
      if(fi == f_ex)
        continue; 
      if(!ub(flows[fi].at))
        expl.push(flows[fi].at);
      if(lb(flows[fi].at))
        expl.push(~flows[fi].at);
    }
#else
    queue.clear();
    src_blocked.clear(); sink_blocked.clear();
    sink_blocked.add(di);

    queue.push((di<<1)|1);
    int qi = 0;
    for(; qi < queue.size(); ++qi) {
      int e = queue[qi];

      if(!(e&1)) {
        // Source node
        for(int fi : out_flows[e>>1]) {
          if(fi == f_ex)
            continue;
          if(used_flow[fi] == !S)
            continue;
          const bflow& f(flows[fi]);
          if(sink_seen.elem(f.sink)) {
            EX_PUSH(expl, S ? ~f.at : f.at);
          } else {
            if(!sink_blocked.elem(f.sink)) {
              sink_blocked.add(f.sink);
              queue.push((f.sink<<1)|1);
            }
          }
        }
      } else {
        // Sink node
        for(int fi : in_flows[e>>1]) {
          if(fi == f_ex)
            continue;
          if(used_flow[fi] == S)
            continue;
          const bflow& f(flows[fi]);
          if(src_seen.elem(f.src)) {
            EX_PUSH(expl, S ? f.at : ~f.at);
          } else {
            if(!src_blocked.elem(f.src)) {
              src_blocked.add(f.src);
              queue.push(f.src<<1);
            }
          }
        }
      }
    }
#endif
    src_blocked.clear();
    sink_blocked.clear();
    queue.clear();
  }

  template<int S>
  bool mark_reach(int si, int di, int blocked_fi = -1) {
    src_seen.clear(); sink_seen.clear();
    src_seen.add(si);
    queue.clear();
    queue.push(si<<1);

    int qi = 0;
    for(; qi < queue.size(); ++qi) {
      int e = queue[qi];
      if(!(e&1)) {
        // Searching forward.
        for(int fi : out_flows[e>>1]) {
          if(fi == blocked_fi)
            continue;
          const bflow& f(flows[fi]);
          if(S) {
            if(used_flow[fi] || sink_seen.elem(f.sink) || !ub(f.at))
              continue;
          } else {
            if(!used_flow[fi] || sink_seen.elem(f.sink) || lb(f.at))
              continue;
          }

          sink_pred[f.sink] = fi;
          if(f.sink == di)
            return true;

          sink_seen.add(f.sink);
          queue.push((f.sink<<1)|1);
        }
      } else {
        // Searching backward
        for(int fi : in_flows[e>>1]) {
          if(fi == blocked_fi)
            continue;
          const bflow& f(flows[fi]);
          if(S) {
            if(!used_flow[fi] || src_seen.elem(f.src) || lb(f.at))
              continue;
          } else {
            if(used_flow[fi] || src_seen.elem(f.src) || !ub(f.at))
              continue;
          }
          src_pred[f.src] = fi;
          src_seen.add(f.src);
          queue.push(f.src<<1);
        }
      }
    }
    return false;
  }

  template<int S>
  bool find_sink(int si, vec<int>& slack) {
    src_seen.clear(); sink_seen.clear();
    src_seen.add(si);
    queue.clear();
    queue.push(si<<1);

    int qi = 0;
    for(; qi < queue.size(); ++qi) {
      int e = queue[qi];
      if(!(e&1)) {
        // Searching forward.
        for(int fi : out_flows[e>>1]) {
          const bflow& f(flows[fi]);
          if(S) {
            if(used_flow[fi] || sink_seen.elem(f.sink) || !ub(f.at))
              continue;
          } else {
            if(!used_flow[fi] || sink_seen.elem(f.sink) || lb(f.at))
              continue;
          }

          sink_pred[f.sink] = fi;
          if(slack[f.sink]) {
            // Now fix the path
            slack[f.sink]--;

            int dflow = fi;
            int src = f.src;
            while(src != si) {
              used_flow[dflow] = S;
              int sflow = src_pred[src];
              used_flow[sflow] = !S;
              dflow = sink_pred[flows[sflow].sink];
              src = flows[dflow].src;
            }
            used_flow[dflow] = S;

            return true;
          }

          sink_seen.add(f.sink);
          queue.push((f.sink<<1)|1);
        }
      } else {
        // Searching backward
        for(int fi : in_flows[e>>1]) {
          const bflow& f(flows[fi]);
          if(S) {
            if(!used_flow[fi] || src_seen.elem(f.src) || lb(f.at))
              continue;
          } else {
            if(used_flow[fi] || src_seen.elem(f.src) || !ub(f.at))
              continue;
          }
          src_pred[f.src] = fi;
          src_seen.add(f.src);
          queue.push(f.src<<1);
        }
      }
    }
    return false;
  }

  template<int S>
  bool init_flow(int si, int di) {
    if(!mark_reach<S>(si, di))
      return false;

    int dflow = sink_pred[di];
    int src = flows[dflow].src;
    while(src != si) {
      used_flow[dflow] = S;
      int sflow = src_pred[src];
      used_flow[sflow] = !S;
      dflow = sink_pred[flows[sflow].sink];
      src = flows[dflow].src;
    }
    used_flow[dflow] = S;
    return true;
  }

  template<int S>
  bool repair_flow(int f0) {
    int si = flows[f0].src;
    int di = flows[f0].sink;
    if(!init_flow<S>(si, di))
      return false;
    used_flow[f0] = !S;
    return true;
  }

public:
  bp_flow_int(solver_data* s, vec<int>& srcs, vec<int>& sinks,
    vec<bflow>& _flows)
    : propagator(s)
    , src_seen(srcs.size()), sink_seen(sinks.size())
    , src_blocked(srcs.size()), sink_blocked(sinks.size())
    , sccs(2 * std::max(srcs.size(), sinks.size()), 0)
    , lowlink(2 * std::max(srcs.size(), sinks.size()), 0)
    , index(2 * std::max(srcs.size(), sinks.size()))
    , queued(2 * std::max(srcs.size(), sinks.size()), false) {
    // Initialize the graph.
    for(int ii = 0; ii < srcs.size(); ii++) {
      out_flows.push();
      src_pred.push(0);
    }
    for(int ii = 0; ii < sinks.size(); ii++) {
      in_flows.push();
      sink_pred.push(0);
    }
    for(bflow& f : _flows) {
      // Drop false flows.
      if(s->state.is_inconsistent(f.at))
        continue;
      // If the flow is definitely true, just
      // decrease the corresponding src/sink.
      if(s->state.is_entailed(f.at)) {
        srcs[f.src] -= 1;          
        sinks[f.sink] -= 1;
        continue;
      }
      int fi = flows.size();
      flows.push(f);
      used_flow.push(0);
      attach(s, f.at, watch<&P::wake_fix>(fi, Wt_IDEM));
      attach(s, ~f.at, watch<&P::wake_kill>(fi, Wt_IDEM));
      out_flows[f.src].push(fi);
      in_flows[f.sink].push(fi);
    }

    // Now we need to find an initial feasible flow.
    // This is a hideously inefficient way of initialization.
    // int di = 0;
    for(int si = 0; si < srcs.size(); si++) {
      while(srcs[si]) {
        /*
        while(!sinks[di]) ++di;
        if(!init_flow<true>(si, di))
          GEAS_ERROR;
          */
        if(!find_sink<true>(si, sinks))
          GEAS_ERROR;
        srcs[si]--;
        // sinks[di]--;
        src_seen.clear();
        sink_seen.clear(); 
        queue.clear();
      }
    }
  }

  // Implementing Tarjan's algorithm.
  void strongconnect(int e) {
    int v = e>>1;
    index.insert(e);
    lowlink[e] = index.pos(e);
    queue.push(e);
    queued[e] = true;

    if(!(e&1)) {
      for(int fi : out_flows[v]) {
        // Forward in residual if not used, but unfixed
        if(!used_flow[fi] && ub(flows[fi].at)) {
          int d = (flows[fi].sink<<1)|1;
          if(!index.elem(d)) {
            strongconnect(d);
            lowlink[e] = std::min(lowlink[e], lowlink[d]);
          } else if (queued[d]) {
            lowlink[e] = std::min(lowlink[e], (int) index.pos(d));
          }
        }
      }
    } else {
      // Sink node
      for(int fi : in_flows[v]) {
        // Backward in residual if used, but not mandatory.
        if(used_flow[fi] && !lb(flows[fi].at)) {
          int s = flows[fi].src<<1;
          if(!index.elem(s)) {
            strongconnect(s);
            lowlink[e] = std::min(lowlink[e], lowlink[s]);
          } else if (queued[s]) {
            lowlink[e] = std::min(lowlink[e], (int) index.pos(s));
          }
        }
      }
    }
    // Root node?
    if(lowlink[e] == index.pos(e)) {
      int w;
      do {
        w = queue.last();
        queue.pop();
        queued[w] = false;
        sccs[w] = e;
      } while(w != e);
    }
  }

  void compute_sccs(void) {
    index.clear();
    queue.clear();
    for(int ii : irange(out_flows.size())) {
      int e = ii<<1;
      if(!index.elem(e))
        strongconnect(e);
    }
    for(int ii: irange(in_flows.size())) {
      int e = (ii<<1)|1;
      if(!index.elem(e))
        strongconnect(e);
    }
  }
  bool process_sccs(vec<clause_elt>& confl) {
    for(int fi : irange(flows.size())) {
      bflow& f(flows[fi]);
      if(sccs[f.src<<1] != sccs[(f.sink<<1)|1]) {
        if(used_flow[fi] && !lb(f.at)) {
          if(!enqueue(*s, f.at,
              ex_thunk(ex<&P::ex_pos>, fi, expl_thunk::Ex_BTPRED)))
            return false;
        } else if(!used_flow[fi] && ub(f.at)) {
          if(!enqueue(*s, ~f.at,
              ex_thunk(ex<&P::ex_neg>, fi, expl_thunk::Ex_BTPRED)))
            return false;
        }
      }
    }
    return true;
  }

  bool propagate(vec<clause_elt>& confl) {
    // fprintf(stderr, "[Running bipartite-flow (%d)]\n", prop_id);
    // Try to repair the model
    for(int fi : fixed_flows) {
      if(!used_flow[fi]) {
        if(!repair_flow<false>(fi)) {
          EX_PUSH(confl, ~flows[fi].at);
          make_expl<false>(fi, flows[fi].src, flows[fi].sink, confl);
          return false;
        }
      }
    }
    for(int fi : dead_flows) {
      if(used_flow[fi]) {
        if(!repair_flow<true>(fi)) {
          EX_PUSH(confl, flows[fi].at);
          make_expl<true>(fi, flows[fi].src, flows[fi].sink, confl);
          return false;
        }
      }
    }

    // In the residual graph, only
    // flows within an SCC could be used.
    compute_sccs();
#ifdef LOG_FLOW
    fprintf(stderr, "After repair:\n");
    log_state();
#endif
    if(!process_sccs(confl))
      return false;

#ifdef LOG_FLOW
    fprintf(stderr, "After propagation:\n");
    log_state();
#endif
    return true;
  }

  void cleanup(void) {
    is_queued = false;
    fixed_flows.clear();
    dead_flows.clear();

    src_seen.clear();
    sink_seen.clear();
    queue.clear();
  }

  // Flow definitions.
  vec< vec<int> > out_flows;
  vec< vec<int> > in_flows;
  vec<bflow> flows;
  
  // Persistent state: which
  // flows are used in the current model.
  vec<bool> used_flow;

  // Transient state
  vec<int> fixed_flows;
  vec<int> dead_flows;
  
  // Bookkeeping for repair
  boolset src_seen;
  boolset sink_seen;
  boolset src_blocked;
  boolset sink_blocked;
  vec<int> src_pred;
  vec<int> sink_pred;

  // Bookkeeping for propagation
  vec<int> sccs;
  vec<int> lowlink;
  p_sparseset index;
  vec<bool> queued;

  vec<int> queue;
};

bool bipartite_flow(solver_data* s, vec<int>& srcs, vec<int>& sinks, vec<bflow>& flows) {
  new bp_flow_int(s, srcs, sinks, flows);
  return true; 
}

#if 0
struct arc_t {
  int src;
  patom_t at; 
  int dest;
};

struct darc_t {
  patom_t at;
  int dest;
};

// For now,
/*
struct node_t {
  enum Kind { S_Fix, S_Var };
  struct cap { int lb; int ub; };

  Kind kind;
  union {
    cap c;
    intvar v;
  };

  inline int lb(ctx_t& ctx) const {
    return kind == S_Var ? v.lb(ctx) : c.lb;
  }
  inline int ub(ctx_t& ctx) const {
    return kind == S_Var ? v.ub(ctx) : c.ub;
  }
};
*/
struct node_t {
  int lb;
  int ub;
};

struct adjs_t {
  vec<int> arc_id;
  int deg;
};

#define ARC_ID(tag) ((tag)>>1)
#define ARC_SIGN(tag) ((tag)&1)

class bipartite_matching :
  public propagator, public prop_inst<bipartite_matching> {
public:
  watch_result wake_arc(int tag) {
    int aid = ARC_ID(tag);
    bool sign = ARG_SIGN(tag);

    if(used(aid) != sign) {
      repair_queue.push(tag);
      queue_prop();
    }
    return Wt_Keep;
  }

  void cleanup(void) {
    in_queue = false;
    repair_queue.clear(); 
  }

  bipartite_matching(solver_data* s,
    vec<node_t>& srcs, vec<node_t>& sinks,
    vec<arc_t>& arcs);

  bool propagate(vec<clause_elt>& confl);

  // Problem info.
  vec<node_t> sources;
  vec<node_t> sinks;

  vec<arc_t> arcs;

  vec<adjs_t> fwd;
  vec<adjs_t> rev;

  // State
  vec<int> sink_flow;
  vec<int> source_flow;

  // Transient data
  boolset sink_seen;
  boolset source_seen;

  // Queue of arcs to repair
  vec<int> repair_queue;
};

bool bipartite(vec<intvar>& ) {

  return true; 
}

template<class Ctx, class V>
inline int vars_lb(Ctx& ctx, vec<V>& xs) {
  int lb_xs = std::accumulate(&xs[1], xs.end(), xs[0].lb(s),
    [](int k, intvar y) { std::min(k, y.lb(ctx)); });
}

template<class Ctx, class V>
inline int vars_ub(Ctx& ctx, vec<V>& xs) {
  int lb_xs = std::accumulate(&xs[1], xs.end(), xs[0].ub(s),
    [](int k, intvar y) { std::max(k, y.ub(ctx)); });
}


bool alldifferent(solver_data* s, vec<intvar>& xs) {
  // Compute the min/max of the variables.
  int lb_xs = vars_lb(s, xs);
  int ub_xs = vars_ub(s, xs);

  vec<sink_t> sources;
  vec<sink_t> sinks;
  vec<arc_t> arcs;   

  // Set up sink capacities
  int nsinks = ub_xs - lb_xs + 1;
  int min_flow = (nsinks == xs.size()) ? 1 : 0;

  for(int ii : irange(nsinks)) {
    sinks.push(node_t { min_flow, 1 });
  }

  // Set up edges
  for(int xi : irange(xs.size())) {
    intvar x = xs[xi];
    sources.push(node_t { 1, 1 });
    for(int k : x.domain(s)) {
      arcs.push(arc_t { xi, x = k, k - xs_lb });
    }
  }

  return bipartite_match(s, sources, sinks, arcs);
}

bool alldifferent_except_k(solver_data* s, vec<intvar>& xs, int k) {
  // Compute the range.
  int xs_lb = vars_lb(s, xs);
  int xs_ub = vars_ub(s, xs);
  
  int nsinks = xs_ub - xs_lb + 1; 

  vec<node_t> sources;
  vec<node_t> sinks;
  vec<arc_t> arcs;

  int ki = k - xs_lb;

  // lb(xs) .. k-1
  for(int ii : irange(ki)) {
    sinks.push(node_t { 0, 1 });
  }
  // k
  sinks.push(node_t { 0, xs.size() });
  // k+1 .. ub(xs)
  for(int ii : irange(ki+1, nsinks)) {
    sinks.push(node_t { 0, 1 });
  }

  for(int xi : irange(xs.size())) {
    intvar x = xs[xi];
    sources.push(node_t { 1, 1 });
    
    for(int v : x.domain(s)) {
      arcs.push(arc_t { xi, x = v, v - x_lb });
    }
  }

  return bipartite_match(s, sources, sinks, arcs);
}

// forall i j, x[i] = j+k <-> y[j] = i+k.
bool inverse(vec<intvar>& xs, vec<intvar>& ys, int k) {
  // TODO: Integrate this properly.
  if(!all_different(s, xs) || !all_different(s, ys))
    return false;
    
  for(int ii : irange(xs.size())) {
    for(int jj : irange(ys.size())) {
      // xs[ii] = j+k <-> ys[jj] = i+k.
      patom_t x_ij = (xs[ii] == j+k);
      patom_t y_ji = (ys[jj] == i+k); 
      if(!add_clause(s, x_ij, ~y_ji))
        return false;
      if(!add_clause(s, ~x_ij, y_ji))
        return false;
    }
  }
  return true;
}

bipartite_matching::bipartite_matching(solver_data* s,
    vec<node_t>& _srcs, vec<node_t>& _sinks,
    vec<arc_t>& _arcs)
    : srcs(_srcs), sinks(_sinks), arcs(_arcs) {
  // Set up initial solution
}

bool bipartite_matching::propagate(vec<clause_elt>& confl) {
  for(int tag : repair_queue) {
    int ai = ARC_ID(tag);
    int sign = ARC_SIGN(tag);

    if(sign) { 
      if(!set_arc(ai, confl))
        return false;
    } else {
      if(!kill_arc(ai, confl))
        return false;
    }
  }
  repair_queue.clear();
  return true;
}

#endif

}
