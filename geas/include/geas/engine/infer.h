#ifndef GEAS_INFER__H
#define GEAS_INFER__H
#include <map>
#include <vector>

#include <geas/mtl/int-triemap.h>
#include <geas/engine/infer-types.h>

// #define SPARSE_WATCHES

namespace geas {

class infer_info {
public:
  struct bin_le { pid_t p; spval_t offset; };

  // Predicates 0 and 1 are placeholders, and always
  // exist.
  infer_info(void) {
    // Done by solver_data constructor
    // new_pred();
  }

  ~infer_info(void) {
    // Clear watches
    watch_maps.clear();
    for(watch_head h : pred_watch_heads) {
      watch_node* p = h.ptr;
      while(p) {
        watch_node* s = p->succ;
        delete p;
        p = s;
      }
    }
    
    // Then clauses and learnts
    for(clause* c : clauses)
      free(c);
    for(clause* l : learnts)
      free(l);
  }

  // Predicates should only be added in pairs.
  pid_t new_pred(void) {
    pid_t p = new_half_pred();
    new_half_pred();
    pred_act.push(0.0);
    return p;
  }

  pid_t new_pred(pval_t lb, pval_t ub) {
    pid_t p = new_half_pred(lb, ub);
    new_half_pred(pval_inv(ub), pval_inv(lb));
    pred_act.push(0.0);
    return p;
  }

  void growTo(int sz) {
    while(watch_maps.size() <= sz)
      new_pred();
  }

  void root_simplify(void) {
    trail.clear();
    trail_lim.clear();
  }

protected:
  pid_t new_half_pred(void) {
    pid_t pid = watch_maps.size();
    // Create the root watch-node
#if 1
    watch_node* w(new watch_node); 
    // w->atom = patom_t(pid, 0);
#ifdef DEBUG_WMAP
    w->curr_val = 0;
#endif
    // w->succ_val = pval_max;
    w->succ_val = pval_err;
    pred_watches.push(w);
    pred_watch_heads.push(watch_head {0, w});
//    pred_act.push(0.0);

    pred_ineqs.push();

    watch_maps.push();
    watch_maps.last().add(0, w);
#else
    pred_ineqs.push();
    watch_maps.push();
    watch_node* w(watch_maps.last().get(0));
    pred_watches.push(w);
    pred_watch_heads.push(watch_head {0, w});
#endif
    return pid;
  }

  pid_t new_half_pred(pval_t lb, pval_t ub) {
    pid_t pid = watch_maps.size();
    pred_ineqs.push();
#ifndef SPARSE_WATCHES
    watch_node* w(new watch_node); 
#ifdef DEBUG_WMAP
    w->curr_val = 0;
#endif
    w->succ_val = pval_err;
    pred_watches.push(w);
    pred_watch_heads.push(watch_head {0, w});

    pred_ineqs.push();
    watch_maps.push();
    watch_maps.last().add(0, w);
#else
    watch_maps.push(watch_map(lb, ub));
    watch_node* w(watch_maps.last().get(lb));
    pred_watches.push(w);
    pred_watch_heads.push(watch_head {lb, w});
#endif

    return pid;
  }

public:
  // Get the watch for an atom, knowing it exists.
  watch_node* lookup_watch(pid_t p, pval_t val) {
    uint64_t key = (uint64_t) val;
    watch_map::iterator it = watch_maps[p].find(key);
    if(it == watch_maps[p].end())
      GEAS_ERROR;
    return (*it).value;
  }

  // Find the appropriate watch for an atom.
  watch_node* get_watch(pid_t p, pval_t val) {
#ifdef SPARSE_WATCHES
    /*
    MakeWNode m;
    return (*(watch_maps[p].find_or_add(m, key))).value;
    */
    return watch_maps[p].get(val);
#else
    uint64_t key = (uint64_t) val;
    watch_map::iterator it = watch_maps[p].find(key);
    if(it != watch_maps[p].end()) 
      return (*it).value;
    watch_node* w(new watch_node);
    // w->atom = patom_t(p, val);

    // This repeats the lookup performed by
    // find. Modify to avoid this.
    it = watch_maps[p].add(key, w);
    --it;
    watch_node* pred = (*it).value;
#ifdef DEBUG_WMAP
    w->curr_val = val;
    assert(pred->curr_val < val);
#endif
    w->succ_val = pred->succ_val;
    w->succ = pred->succ;
    pred->succ_val = val;
    pred->succ = w;
    return w;
#endif
  }

  void make_sparse(pid_t p, vec<pval_t>& vs) {
#ifdef SPARSE_WATCHES
    // Only safe at decision level 0.
    watch_maps[p].make_sparse(p, vs); 
    watch_node* w(watch_maps[p].nodes);
    pred_watches[p] = w;
    pred_watch_heads[p] = watch_head { 0, w };
#endif
  }

  struct entry {
    pid_t pid;
    pval_t old_val;
    reason expl;
  };
  
  struct watch_head {
    pval_t val;
    watch_node* ptr;
  };

  // Tracking watch lists for predicates
  vec<watch_map> watch_maps; // (pid_t -> pval_t -> watch_node*)
  vec<watch_node*> pred_watches;
  vec<watch_head> pred_watch_heads; // Watches for [| pid >= min_val |].
  vec<double> pred_act;

  vec< vec<bin_le> > pred_ineqs; // Primitive binary inequalities

  // Inference graph and backtracking
  vec<int> trail_lim;
  vec<entry> trail;

  // Temporary storage for the conflict
  vec<clause_elt> confl;  

  vec<clause*> clauses;
  vec<clause*> learnts;
};

}
#endif
