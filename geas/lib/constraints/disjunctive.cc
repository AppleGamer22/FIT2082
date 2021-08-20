#include <climits>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/vars/intvar.h>
namespace geas {

// Helpful functions
static unsigned int tree_sz(unsigned int leaves) {
  unsigned int pow = 33 - __builtin_clz(leaves-1);
  return (1<<pow)-1;
}
static unsigned int parent(unsigned int p) { return (p-1)>>1; };
static unsigned int left(unsigned int p) { return (p<<1)+1; };
static unsigned int right(unsigned int p) { return (p<<1)+2; };
// Heap-structured complete binary tree.
template<class F>
struct ps_tree {
  // Node data.
  struct node_t {
    int d_sum;
    int ect;
    int o_sum;
    int o_ect;
  };

  unsigned int base(void) const { return nodes.size()/2; }
  unsigned int idx(unsigned int n) const { return n + nodes.size()/2; };

  ps_tree(F _f, unsigned int leaves)
    : f(_f)
    , nodes(tree_sz(leaves), node_t { 0, INT_MIN, 0, INT_MIN })
    , sz(leaves)
  { }
  
  node_t eval(const node_t& l, const node_t& r) {
    node_t n {
        l.d_sum + r.d_sum,
        std::max(l.ect + r.d_sum, r.ect),
        std::max(l.d_sum + r.o_sum, l.o_sum + r.d_sum),
        std::max(r.o_ect,
          std::max(l.ect + r.o_sum, l.o_ect + r.d_sum))
    };
    return n;
  }

  void fill(void) {
    unsigned int idx = nodes.size()/2;  
    for(int ii = 0; ii < sz; ++ii, ++idx) {
      int ect = f.ect(ii);
      int dur = f.dur(ii); 
      nodes[idx] = { dur, ect, dur, ect };
    }
    for(int p = base()-1; p >= 0; --p) {
      node_t& l(nodes[left(p)]);
      node_t& r(nodes[right(p)]);
      nodes[p] = eval(l, r);
    }
  }

  void percolate(unsigned int p) {
    while(p) {
      node_t& l(p&1 ? nodes[p] : nodes[p-1]);
      node_t& r(p&1 ? nodes[p+1] : nodes[p]);
      p = parent(p);
      nodes[p] = eval(l, r);
    }
  }
  
  void add(unsigned int elt) {
    int dur = f.dur(elt);
    int ect = f.ect(elt);
    
    unsigned int p(idx(elt));
    nodes[p] = node_t { dur, ect, dur, ect };
    percolate(p);
  }
  void remove(unsigned int elt) {
    unsigned int p(idx(elt));
    nodes[p] = node_t { 0, INT_MIN, 0, INT_MIN };
    percolate(p);
  }
  void smudge(unsigned int elt) {
    // Assumes elt is currently in.
    unsigned int p(idx(elt));
    nodes[p].d_sum = 0;
    nodes[p].ect = INT_MIN;
    percolate(p);
  }

  // Find the task whose start time bounds
  // the current envelope.
  unsigned int binding_task(int ect, unsigned int p = 0) {
    assert(nodes[0].ect >= ect);
    // unsigned int p = 0;
    while(p < base()) {
      if(nodes[right(p)].ect >= ect) {
        p = right(p);
      } else {
        ect -= nodes[right(p)].d_sum;
        p = left(p);
      }
    }
    return p - base();
  }

  // Find the smudged task responsible for
  // pushing the ECT above the given limit.
  unsigned int blocked_task(int ect) {
    assert(nodes[0].ect < ect);
    assert(nodes[0].o_ect >= ect);
    unsigned int p = 0;
    while(p < base()) {
      if(nodes[right(p)].o_ect >= ect) {
        p = right(p);
      } else if(nodes[left(p)].ect + nodes[right(p)].o_sum >= ect) {
        // The binding task is to the left, blocked task contributes
        // only to the sum.
        ect -= nodes[left(p)].ect;
        p = right(p);
        while(p < base()) {
          if(nodes[left(p)].d_sum + nodes[right(p)].o_sum >= ect) {
            ect -= nodes[left(p)].d_sum;
            p = right(p);
          } else {
            ect -= nodes[right(p)].d_sum;
            p = left(p);
          }
        }
        break;
      } else {
        ect -= nodes[right(p)].d_sum;
        p = left(p);
      }
    }
    return p - base();
  }

  // If there is a blocked task, which task is binding
  // in the corresponding set?
  unsigned int blocking_task(int ect) {
    assert(nodes[0].ect < ect);
    assert(nodes[0].o_ect >= ect);
    unsigned int p = 0;
    while(p < base()) {
      if(nodes[right(p)].o_ect >= ect) {
        p = right(p);
      } else if(nodes[left(p)].ect + nodes[right(p)].o_sum >= ect) {
        return binding_task(ect - nodes[right(p)].o_sum, left(p));
      } else {
        ect -= nodes[right(p)].d_sum;
        p = left(p);
      }
    }
    return p - base();
  }

  const node_t& root(void) const { return nodes[0]; };
  const node_t& operator[](unsigned int p) const { return nodes[p]; }

  F f;
  vec<node_t> nodes;
  int sz;
};

class disjunctive : public propagator, public prop_inst<disjunctive> {
  struct eval_ect {
    int ect(int idx) const {
      return d->ect(d->p_est[idx]);
    }
    int dur(int idx) const { return d->du[d->p_est[idx]]; }

    disjunctive* d;
  };
  struct eval_lst {
    int ect(int idx) const {
      return -d->lst(d->p_lct[idx]);
    }
    int dur(int idx) const { return d->du[d->p_lct[idx]]; }
    disjunctive* d;
  };

  inline int est(int xi) { return lb(xs[xi]); }
  inline int ect(int xi) { return lb(xs[xi]) + du[xi]; }
  inline int lct(int xi) { return ub(xs[xi]) + du[xi]; }
  inline int lst(int xi) { return ub(xs[xi]); }

  // For semi-eager explanations
  struct ex_data {
    int xi; // Task which was updated
    int lb; // est of energy window
    int ub; // lct of energy window
  };

  watch_result wake(int xi) {
    queue_prop();
    return Wt_Keep;
  }
  
  int LOW(int x) { return x&((1<<16)-1); }
  int HIGH(int x) { return x>>16; }
  int TAG(int x, int y) { return (y<<16)|x; }
  
  void ex_naive(int _x, pval_t p, vec<clause_elt>& expl) {
    for(const intvar& x : xs) {
      expl.push(x < lb(x));
      expl.push(x > ub(x));
    }
  }

  bool check_sat(ctx_t& ctx) {
    // Identify the envelope starts.
    vec<int> ss;
    vec<int> e_perm;
    for(int xi : irange(xs.size())) {
      ss.push(xs[xi].lb(ctx));
      e_perm.push(xi);
    }
    uniq(ss);
    std::sort(e_perm.begin(), e_perm.end(),
      [this, &ctx](int i, int j) { return xs[i].ub(ctx) + du[i] < xs[j].ub(ctx) + du[j]; });

    // For each possible start, check if there is any over-full envelope
    // it defines.
    for(int s : ss) {
      int ect = s;
      for(int t : e_perm) {
        if(s <= xs[t].lb(ctx)) {
          // Contained in the envelope
          ect += du[t]; 
          if(xs[t].ub(ctx) < ect)
            return false;
        }
      }
    }
    return false;
  }
  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

  // TODO: Explanation lifting
  void ex_lb_ef_eager(int eid, pval_t p, vec<clause_elt>& expl) {
    ex_data e(edata[eid]);
    // int x_lb = xs[e.xi].lb_of_pval(p);
    // assert(e.ub >= x_lb + du[e.xi]);

    // Need to collect at least ub - lb - du[xi] energy,
    // from tasks bracketed in [lb, ub]
    expl.push(xs[e.xi] < e.lb);
    int energy = e.ub - e.lb - du[e.xi];
    for(int ti : irange(xs.size())) {
      if(ti == e.xi)
        continue;
      if(est(ti) < e.lb || lct(ti) > e.ub)
        continue;
      EX_PUSH(expl, xs[ti] < e.lb);
      EX_PUSH(expl, xs[ti] > e.ub - du[ti]);
      energy -= du[ti];
      if(energy <= 0)
        break; 
    }
    assert(energy <= 0);
  }

  void ex_ub_ef_eager(int eid, pval_t p, vec<clause_elt>& expl) {
    ex_data e(edata[eid]);

    expl.push(xs[e.xi] >= e.ub);
    int energy = e.ub - e.lb - du[e.xi];
    for(int ti : irange(xs.size())) {
      if(ti == e.xi)
        continue;
      if(est(ti) < e.lb || lct(ti) > e.ub)
        continue;
      EX_PUSH(expl, xs[ti] < e.lb);
      EX_PUSH(expl, xs[ti] > e.ub - du[ti]);
      energy -= du[ti];
      if(energy <= 0)
        break; 
    }
    assert(energy <= 0);
  }

  void ex_lb_ef(int xy, pval_t p, vec<clause_elt>& expl) {
    int x = LOW(xy);
    int y = HIGH(xy); 

    /*
    ex_naive(xy, p, expl);
    return;
    */

    // int lb_x = xs[x].lb_of_pval(p) + du[x];
    int lb_x = xs[x].lb_of_pval(p);
    int lb_y = lb(xs[y]);
    // Collect enough tasks to fill [est(y), lb_x).
    vec<int> ex_tasks;
    for(int ii : irange(xs.size())) {
      if(est(ii) >= lb_y)
        ex_tasks.push(ii);
    }
    std::sort(ex_tasks.begin(), ex_tasks.end(), 
      [&](int ti, int tj) { return lct(ti) < lct(tj); });

    /*
    int gap = lb_x - lb_y;
    for(int ii : irange(xs.size())) {
      if(ii == x)
        continue;
      if(est(ii) >= lb_y && lct(ii) <= lb_x) {
        expl.push(xs[ii] < lb_y);
        expl.push(xs[ii] > lb_x - du[ii]);
        gap -= du[ii];
        // TODO: Can weaken here if gap < 0.
        if(gap <= 0)
          break;
      }
    }
    */
    int energy = 0;
    int eend = lb_y;
    int end = lb_x;
    int ii = 0;
    for(; ii < ex_tasks.size(); ++ii) {
      energy += du[ex_tasks[ii]];
      eend += du[ex_tasks[ii]];
      end = std::max(end, lct(ex_tasks[ii]));
      if(eend + du[x] > lct(ex_tasks[ii])
        && eend >= end)
        break;
    }
    ex_tasks.shrink(ex_tasks.size() - ii);

    int begin = end - energy;
    for(int xi : ex_tasks) {
      expl.push(xs[xi] < begin);
      expl.push(xs[xi] >= end - du[xi]);
    }
  }
  void ex_ub_ef(int xy, pval_t p, vec<clause_elt>& expl) {
    /*
    int x = LOW(xy);
    int y = HIGH(xy);
    */
    
    ex_naive(xy, p, expl);
/*
    int ub_x = xs[x].ub_of_pval(p);
    int ub_y = ub(xs[y]) + du[y];
    int gap = ub_y - ub_x;
    for(int ii : irange(xs.size())) {
      if(ii == x)
        continue;
      // FIXME: Probably an off-by-one somewhere here
      if(est(ii) >= ub_x && lct(ii) <= ub_y) {
        expl.push(xs[ii] < ub_x - du[ii]);
        expl.push(xs[ii] > ub_y - du[ii]);
        gap -= du[ii];
      }
      if(gap <= 0)
        break;
    }
    assert(gap <= 0);
    */
  }

  public:
    disjunctive(solver_data* s, vec<intvar>& _st, vec<int>& _du)
      : propagator(s), xs(_st), du(_du)
      , ect_tree(eval_ect {this}, xs.size())
      , lst_tree(eval_lst {this}, xs.size())
      , edata_saved(false) {
      for(int ii : irange(xs.size())) {
        xs[ii].attach(E_LU, watch<&P::wake>(ii));
        p_est.push(ii);
        p_lct.push(ii);
        task_idx.push(ii);
      }
    }

    // Make enough information to reconstruct an explanation
    int make_edata(int xi, int lb, int ub) {
      int id = edata.size();
      trail_save(s->persist, edata._size(), edata_saved);
      edata.push(ex_data { xi, lb, ub });
      return id;
    }

    void cleanup(void) {
      is_queued = false;
    }

    void root_simplify(void) {
      return; 
    }
    
    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running disjunctive]]" << std::endl;
#endif
      return prop_ef(confl);      
    }

    void check_envelope(int t, int lb, int ub) {
      int energy = ub - lb - du[t];
      for(int xi : irange(xs.size())) {
        if(xi == t)
          continue;
        if(lb <= est(xi) && lct(xi) <= ub)
          energy -= du[xi];
      }
      assert(energy < 0);
    }
    // Explain why ECT >= end. 
    // Returns 
    int ex_ect(int end, vec<clause_elt>& confl) {
      int p = ect_tree.binding_task(end);
      int xi = p_est[p];

      vec<int> e_tasks;

      // Have a choice as to which side to relax.
      int lb = est(xi);
      int slack = end - lb;
      for(; p < p_est.size(); ++p) {
        int xj = p_est[p];
        if(est(xj) >= lb && lct(xj) < end) {
          e_tasks.push(xj);
          slack -= du[xj];
          if(slack <= 0)
            break;
        }
      }
      int r_end = end - slack;
      for(int t : e_tasks) {
        assert(lct(t) < r_end);
        EX_PUSH(confl, xs[t] < lb);
        EX_PUSH(confl, xs[t] >= r_end - du[t]);
      }
      return r_end;
    }

    int ex_lst(int begin, vec<clause_elt>& confl) {
      int p = lst_tree.binding_task(-begin);
      int xi = p_lct[p];

      vec<int> e_tasks;

      // Have a choice as to which side to relax.
      int ub = lct(xi);
      int slack = ub - begin;
      for(; p < p_lct.size(); ++p) {
        int xj = p_lct[p];
        if(est(xj) >= begin && lct(xj) <= ub) {
          e_tasks.push(xj);
          slack -= du[xj];
          if(slack <= 0)
            break;
        }
      }
      int r_begin = begin + slack;
      for(int t : e_tasks) {
        EX_PUSH(confl, xs[t] <= r_begin);
        EX_PUSH(confl, xs[t] > ub - du[t]);
      }
      return r_begin;
    }

    // Perform edge-finding
    bool prop_lb_ef(vec<clause_elt>& confl) {
      // Initialize the phi-sigma tree.
      std::sort(p_est.begin(), p_est.end(), 
        [&](int x, int y) { return est(x) < est(y); });
      ect_tree.fill();
      for(int ii : irange(p_est.size()))
        task_idx[p_est[ii]] = ii;

      std::sort(p_lct.begin(), p_lct.end(),
        [&](int x, int y) { return lct(x) > lct(y); });

      if(ect_tree.root().ect > lct(p_lct[0])) {
        int xi = p_lct[0];
        int lim = ex_ect(lct(p_lct[0])+1, confl);
        EX_PUSH(confl, xs[xi] >= lim - du[xi]);
        return false;
      }
      ect_tree.smudge(task_idx[p_lct[0]]);
      for(int xi : p_lct.slice(1, p_lct.size())) {
        if(ect_tree[0].ect > lct(xi)) {
          // int lim = ex_ect(lct(xi)+1, confl);
//          confl.push(xs[xi] >= lim - du[xi]);
          ex_ect(lct(xi)+1, confl);
          return false;
        }
        while(ect_tree[0].o_ect > lct(xi)) {
          // TODO: This currently takes the largest envelope (up to ect_tree[0].o_ect)
          // But for better explanations, we maybe want the smallest (covering lct(xi)).

          // Identify the failing task.
          int tP(ect_tree[0].o_ect); 
          unsigned int pi = ect_tree.blocked_task(tP);
          unsigned int ti = p_est[pi];
          unsigned int tj = p_est[ect_tree.blocking_task(tP)];
          // fprintf(stdout, "(%d, %d)\n", ti, tj);
          if(lb(xs[ti]) < ect_tree[0].ect) {
            // check_envelope(ti, est(tj), tP-1);
            if(!set_lb(xs[ti], ect_tree[0].ect,
              // ex_thunk(ex<&P::ex_lb_ef>, TAG(ti, tj), expl_thunk::Ex_BTPRED)))
              ex_thunk(ex<&P::ex_lb_ef_eager>, make_edata(ti, est(tj), tP-1), expl_thunk::Ex_BTPRED)))
              // ex_thunk(ex<&P::ex_naive>, TAG(ti, tj), expl_thunk::Ex_BTPRED)))
              return false;
          }
          ect_tree.remove(pi);
        }
        ect_tree.smudge(task_idx[xi]);
      }
      return true;
    }

    // Perform edge-finding
    bool prop_ub_ef(vec<clause_elt>& confl) {
      // Initialize the phi-sigma tree.
      std::sort(p_lct.begin(), p_lct.end(), 
        [&](int x, int y) { return lct(x) > lct(y); });
      lst_tree.fill();
      for(int ii : irange(p_lct.size()))
        task_idx[p_lct[ii]] = ii;

      std::sort(p_est.begin(), p_est.end(),
        [&](int x, int y) { return est(x) < est(y); });

      if(-lst_tree[0].ect < est(p_est[0])) {
        int xi = p_est[0];
        // int lim = ex_lst(lst(xi)+1, confl);
        // confl.push(xs[xi] < lim);
        ex_lst(est(xi)-1, confl);
        return false;
      }
      lst_tree.smudge(task_idx[p_est[0]]);
      for(int xi : p_est.slice(1, p_est.size())) {
        if(-lst_tree[0].ect < est(xi)) {
          int lim = ex_lst(est(xi)-1, confl);
          EX_PUSH(confl, xs[xi] < lim);
          return false;
        }
        while(-lst_tree[0].o_ect < est(xi)) {
          // Identify the failing task.
          int tP(lst_tree[0].o_ect);
          unsigned int pi = lst_tree.blocked_task(tP);
          unsigned int ti = p_lct[pi];
          unsigned int tj = p_lct[lst_tree.blocking_task(tP)];
          if(-lst_tree[0].ect < ub(xs[ti]) + du[ti]) {
            // check_envelope(ti, -tP+1, lct(tj));
            if(!set_ub(xs[ti], -lst_tree[0].ect - du[ti],
              // ex_thunk(ex<&P::ex_ub_ef>, TAG(ti, tj), expl_thunk::Ex_BTPRED)))
              ex_thunk(ex<&P::ex_ub_ef_eager>, make_edata(ti, -tP+1, lct(tj)), expl_thunk::Ex_BTPRED)))
              // ex_thunk(ex<&P::ex_naive>, TAG(ti, tj), expl_thunk::Ex_BTPRED)))
              return false;
          }
          lst_tree.remove(pi);
        }
        lst_tree.smudge(task_idx[xi]);
      }
      return true;
    }

    bool prop_ef(vec<clause_elt>& confl) {
      return prop_lb_ef(confl) && prop_ub_ef(confl);
    }

    // Parameters
    vec<intvar> xs; // Start times
    vec<int> du; // durations

    // Temporary storage
    vec<int> p_est;
    vec<int> p_lct;
    vec<int> task_idx;

    ps_tree<eval_ect> ect_tree;
    ps_tree<eval_lst> lst_tree;

    // For storing explanation information.
    vec<ex_data> edata;
    char edata_saved;
};

bool disjunctive_int(solver_data* s, vec<intvar>& st, vec<int>& du) {
  // new disjunctive(s, st, du);
  // return true;
  return disjunctive::post(s, st, du);
}

bool disjunctive_var(solver_data* s, vec<intvar>& st, vec<intvar>& du) {
  // new disj_var(s, st, du);
  GEAS_NOT_YET;
  return false;
}

}
