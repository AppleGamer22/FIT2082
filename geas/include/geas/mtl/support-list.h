#ifndef GEAS__SUPPORT_LIST__H
#define GEAS__SUPPORT_LIST__H
#include <geas/solver/solver_data.h>
namespace geas {

template<class V>
struct support_list {
  typedef unsigned int node_id;
  struct node { node_id pred; node_id succ; V elt; };
  
  support_list(vec<V>& elts)
    : head(0), tail(elts.size()) {
    if(elts.size() == 0) {
      nodes.push(node { 0, 0 });
    } else {
      nodes.push(node { 0, 1, elts[0] });
      for(int ii : irange(1, elts.size())) {
        nodes.push(node { ii-1, ii+1, elts[ii] });
      }
      nodes.push(node { elts.size()-1, elts.size() });
    }
  }
  
  V support(void) const { return nodes[head].elt; }

  template<class P>
  bool replace_support(solver_data* s, P p) {
    node_id n(head);
    node_id tl(tail);
    assert(n != tl);

    for(n = nodes[n].succ; n != tl; n = nodes[n].succ) {
      node nd(nodes[n]);
      if(P(nd.elt)) {
        // Found a new support. Re-wire the
        // support list.
        node_id old_last = nodes[tl].prec;
        node_id last_rem = nodes[n].prec;

        nodes[old_last].succ = head;    
        nodes[head].pred = old_last;
        nodes[last_rem].succ = tl;
        nodes[tl].prec = last_rem;

        nodes[n].prec = n;
        tail.set(s->persist, head);
        head = n;
        return true;
      }
    }
    tail.set(s->persist, head);
    return false;
  }

  vec<node> nodes;
  node_id head; // Not trailed
  trailed<node_id> tail;
};

template<class V>
struct support_vec {
  typedef unsigned int node_id;
  struct node { node_id pred; node_id succ; V elt; };
  
  support_vec(vec<V>& elts)
    : supports(elts) {
    assert(elts.size() > 0);     
  }
  
  V support(void) const { return supports[0]; }

  template<class P>
  bool replace_support(solver_data* s, P p) {
    assert(!P(supports[0]));
    for(int ii = 1; ii < supports.size(); ++ii) {
      if(P(supports[ii])) {
        std::swap(supports[0], supports[ii]);
        return true;
      }
    }
    return false;
  }
  vec<V> supports;
};

}
#endif
