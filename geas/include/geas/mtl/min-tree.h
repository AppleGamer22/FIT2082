#ifndef GEAS__MIN_TREE__H
#define GEAS__MIN_TREE__H
// Trailed structure for reasoning over the minimum-value of sets.
// Use weak_min_tree if you just need to track the support for a bound, where
// values only increase.
// min_tree allows values to both increase or decrease.
#include <geas/mtl/Vec.h>
#include <geas/solver/solver_data.h>

namespace geas {

template<class V, class E>
class min_tree {
  typedef unsigned int node_id;

  static node_id left_child(node_id n) { return (n<<1) + 1; }
  static node_id right_child(node_id n) { return (n<<1) + 2; }
  static node_id sibling(node_id n) { return (n&1) ? n+1 : n-1; }
  static node_id parent(node_id n) { return (n-1)>>1; }

  node_id node_of(unsigned int v) const { return internal_count + v; }
  unsigned int leaf_of(node_id n) const { return n - internal_count; }
  bool is_internal(node_id n) const { return n < internal_count; }
public: 
  min_tree(solver_data* s, E e, unsigned int leaves)
    : nodes(2*leaves - 1, 0), internal_count(leaves-1), eval(e) {
    initialize(s, 0);
  }

  V initialize(solver_data* s, unsigned int r) {
    if(is_internal(r)) {
      V l_e(initialize(s, left_child(r)));
      V r_e(initialize(s, right_child(r)));
      if(l_e > r_e) {
        nodes[r].set(s->persist, nodes[right_child(r)]); 
        return r_e;
      } else {
        nodes[r].set(s->persist, nodes[left_child(r)]);
        return l_e;
      }
    } else {
      nodes[r].set(s->persist, leaf_of(r));
      return eval(s, leaf_of(r));
    }
  }

  bool increase(solver_data* s, unsigned int v) {
    // Update any nodes where v _was_ the min, and
    // is now dominated by a sibling.
    node_id n(node_of(v));
    unsigned int r(v);
    V r_e(eval(s, r));

    while(n) {
      unsigned int q(nodes[sibling(n)]);
      n = parent(n);
      if(nodes[n] != v)
        return false;

      V q_e(eval(s, q));
      if(q_e >= r_e)
        continue;

      // We've found something better than v.
      nodes[n].set(s->persist, q);
      r = v;
      r_e = q_e;
      while(n) {
        // Finish the tree, but using r instead of v.
        q = nodes[sibling(n)];
        n = parent(n);
        if(nodes[n] != v)
          return false;
        q_e = eval(s, q);
        if(q_e < r_e) {
          r = q;
          r_e = q_e;
        }
        nodes[n].set(s->persist, r);
      }
      return false;
    }
    // Fell through a chain of vs.
    return true;
  }

  bool decrease(solver_data* s, unsigned int v) {
    // Update parents of v, where v is the new min.
    // Returns true if v is the root.
    V v_e(eval(s, v));
    node_id n(node_of(v));

    while(n) {
      n = parent(n);
      if(nodes[n] == v)
        continue;
      V r_e(eval(s, nodes[n]));
      if(v_e >= r_e)
        return false;
      nodes[n].set(s->persist, v);
    }
    // Fell through; v is the root.
    return true;
  }

  template<class F>
  bool forall_lt(F f, solver_data* s, V k) {
    return forall_lt(f, s, 0, k); 
  }

  vec<Tuint> nodes;
  unsigned int internal_count;
  E eval;
protected:
  template<class F>
  bool forall_lt(F f, solver_data* s, node_id n, V k) {
    V n_k(eval(s, nodes[n]));   
    if(k <= n_k) // Cutoff
      return true;
    if(is_internal(n)) {
      return forall_lt(f, s, left_child(n), k)
        && forall_lt(f, s, right_child(n), k);
    } else {
      return f(leaf_of(n));
    }
  }

};

// Variant of the min-tree that is only updated
// when the root changes. Stores lower bounds at
// internal nodes.
template<class V, class E>
class weak_min_tree {
  typedef trailed<V> Tv;
  typedef unsigned int node_id;

  static node_id left_child(node_id n) { return (n<<1) + 1; }
  static node_id right_child(node_id n) { return (n<<1) + 2; }
  static node_id sibling(node_id n) { return (n&1) ? n+1 : n-1; }
  static node_id parent(node_id n) { return (n-1)>>1; }

  node_id node_of(unsigned int v) const { return internal_count + v; }
  unsigned int leaf_of(node_id n) const { return n - internal_count; }
  bool is_internal(node_id n) const { return n < internal_count; }
public: 
  weak_min_tree(solver_data* s, E e, unsigned int leaves)
    : min_elt(0), nodes(2*leaves - 1, 0), internal_count(leaves-1), eval(e) {
    /*
    initialize(s, 0);
    
    node_id r(0);
    while(is_internal(r)) {
      node_id a(left_child(r));
      node_id b(right_child(r));
      if(nodes[a] <= nodes[b])
        r = a;
      else
        r = b;
    }
    min_elt.set(s->persist, leaf_of(r));
    */
  }

  V root_val(void) const { return nodes[0]; }

  void rebuild(solver_data* s, int sz) {
    int cap = 2*sz - 1;
    assert(nodes.size() <= cap);
    nodes.growTo(cap, 0);
    internal_count = sz-1;
    rebuild(s);
  }

  void rebuild(solver_data* s) {
    initialize(s, 0);

    node_id r(0);
    while(is_internal(r)) {
      node_id a(left_child(r));
      node_id b(right_child(r));
      if(nodes[a] <= nodes[b])
        r = a;
      else
        r = b;
    }
    min_elt.set(s->persist, leaf_of(r));
  }

  V initialize(solver_data* s, unsigned int r) {
    if(is_internal(r)) {
      V l_e(initialize(s, left_child(r)));
      V r_e(initialize(s, right_child(r)));
      if(l_e > r_e) {
        nodes[r].set(s->persist, r_e);
        return r_e;
      } else {
        nodes[r].set(s->persist, l_e);
        return l_e;
      }
    } else {
      V e(eval(s, leaf_of(r)));
      nodes[r].set(s->persist, e);
      return e;
    }
  }

  void increase(solver_data* s, unsigned int v) {
    if(v != min_elt)
      return;
    repair_min(s);
  }

  // Returns true if the min value changed.
  bool repair_min(solver_data* s) {
    unsigned int best(min_elt);
    V old(nodes[0]);
    V wt(eval(s, best));

    repair_subtree(s, 0, best, wt);
    if(best != min_elt)
      min_elt.set(s->persist, best);
    return old < wt;
  }

  template<class F>
  bool forall_lt(F f, solver_data* s, V k) {
    bool okay = true;
    forall_lt(f, s, 0, k, okay);
    return okay;
  }

  Tuint min_elt;
  vec<Tv> nodes;
  unsigned int internal_count;
  E eval;

protected:
  V repair_subtree(solver_data* s, node_id r, unsigned int& best, V& best_wt) {
    // Subtree can't improve.
    V curr(nodes[r]);
    if(best_wt <= curr)
      return curr;
    if(is_internal(r)) {
      // Evaluate the node with lowest bound first.
      node_id a(left_child(r));
      node_id b(right_child(r));
      if(nodes[a] > nodes[b]) std::swap(a, b);

      V a_e(repair_subtree(s, a, best, best_wt));
      if(!(curr < a_e))
        return curr;
      V b_e(repair_subtree(s, b, best, best_wt));
      if(!(curr < b_e))
        return curr;
      V ret(std::min(a_e, b_e));
      nodes[r].set(s->persist, ret);
      return ret;
    } else {
      // Leaf node.
      unsigned int v(leaf_of(r));
      V ret(eval(s, v));
      if(ret < best_wt) {
        best = v;
        best_wt = ret;
      }
      if(!(curr < ret))
        return curr;
      nodes[r].set(s->persist, ret);
      return ret;
    }
  }

  template<class F>
  V forall_lt(F f, solver_data* s, node_id r, V k, bool& okay) {
    if(k <= nodes[r])
      return nodes[r];
    if(is_internal(r)) {
      node_id a(left_child(r)); 
      node_id b(right_child(r));
      V a_e(forall_lt(f, s, a, k, okay));
      if(!okay) { // Save an updated bound, and abort.
        V ret(std::min(a_e, (V) nodes[b]));
        if(nodes[r] < ret)
          nodes[r].set(s->persist, ret);
        return ret;
      }
      V b_e(forall_lt(f, s, b, k, okay));
      V ret(std::min(a_e, b_e));
      if(nodes[r] < ret)
        nodes[r].set(s->persist, ret);
      return ret;
    } else {
      unsigned int v(leaf_of(r));
      V ret(eval(s, v));
      if(nodes[r] < ret)
        nodes[r].set(s->persist, ret);
      if(ret < k)
        okay = f(v);
      return ret;
    }
  }
};

template<class V, class E>
class bound_tree {
  typedef unsigned int node_id;

  static node_id left(node_id n) { return (n<<1) + 1; }
  static node_id right(node_id n) { return (n<<1) + 2; }
  static node_id sibling(node_id n) { return (n&1) ? n+1 : n-1; }
  static node_id parent(node_id n) { return (n-1)>>1; }
  node_id base(void) const { return leaves.size()-1; }

  node_id node_of(unsigned int v) const { return v + base(); }
  unsigned int leaf_of(node_id n) const { return n - base(); }
  bool is_internal(node_id n) const { return n < base(); }

public: 
  bound_tree(E e)
    : eval(e), nodes(), leaves() {
    nodes.push(INT_MAX);      
  }

  // TODO: Fix this so we don't need to re-initialize this when a new
  // constraint is added. One solution: prefill layers with int-max,
  // only re-initialize when a level is full.
  int push(V v) {
    int id = leaves.size();
    leaves.push(v);
    if(id) {
      nodes.push();
      nodes.push();
    }
    initialize(0);
    return id;
  }

  int root_val(void) const { return nodes[0]; }

  int initialize(unsigned int r) {
    if(is_internal(r)) {
      int l_e(initialize(left(r)));
      int r_e(initialize(right(r)));
      return nodes[r] = std::min(l_e, r_e);
    } else {
      assert(r < (unsigned int) nodes.size());
      assert(leaf_of(r) < (unsigned int) leaves.size());
      return nodes[r] = eval(leaves[leaf_of(r)]);
    }
  }

  void decrease(unsigned int v) {
    // Update parents of v, where v becomes the
    // subtree min.
    int v_e(eval(leaves[v]));
    node_id n(node_of(v));
    nodes[n] = v_e;

    while(n) {
      n = parent(n);
      if(nodes[n] <= v_e) 
        return;
      nodes[n] = v_e;
    }
  }

  template<class F>
  bool forall_lt(F f, int k) {
    bool okay = true;
    forall_lt(f, 0, k, okay);
    return okay;
  }
protected:
  template<class F>
  int forall_lt(F f, node_id n, int k, bool& okay) {
    // We can guarantee nodes[n] is a lower bound on children of n.
    if(k <= nodes[n])
      return nodes[n];
    if(is_internal(n)) {
      int v_l = forall_lt(f, left(n), k, okay);
      if(!okay) {
        return nodes[n] = std::min(v_l, nodes[right(n)]);
      }
      int v_r = forall_lt(f, right(n), k, okay);
      return nodes[n] = std::min(v_l, v_r);
    } else {
      int l(leaf_of(n));
      if(eval(leaves[l]) < k)
        okay = f(leaves[l]);
      // f might have updated the weight
      return nodes[n] = eval(leaves[l]);
    }
  }

  E eval;
  vec<int> nodes;
  vec<V> leaves;
};

}

#endif
