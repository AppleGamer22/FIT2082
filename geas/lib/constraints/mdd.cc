#include <numeric>
#include <geas/utils/MurmurHash3.h>
#include <geas/solver/solver.h>
#include <geas/solver/solver_ext.h>
#include <geas/constraints/mdd.h>

namespace geas {
  namespace mdd {

class mdd_manager : public solver_ext<mdd_manager> {
public:
   mdd_manager(solver_data* s) { }
  ~mdd_manager(void) {
    for(mdd_info* mi : mdds)
      delete mi;     
  }
   
  mdd_id build(vec< vec<int> >& tuples);
  mdd_info& lookup(mdd_id r) { return *(mdds[r]); }
protected:
  vec<mdd_info*> mdds;
 
};

// TODO: Actually build the MDD.
struct mddfier {
  typedef unsigned int node_id;
  struct edge {
    int val;
    node_id dest;

    bool operator!=(const edge& o) const {
      return val != o.val || dest != o.dest;
    }
  };

  struct key {
    int level;
    int size;
    edge* p;

    edge* begin(void) const { return p; }
    edge* end(void) const { return p + size; }
  };

  mddfier(vec<vec<int> >& _tuples)
    : tuples(_tuples) {
    for(int xi = 0; xi < tuples[0].size(); ++xi)
      levels.push();
  }

  ~mddfier(void) {
    for(vec<key>& l : levels) {
      for(key& k : l)
        free(k.p);
    }
  }

  struct key_eq {
    bool operator()(const key& x, const key& y) const {
      if(x.level != y.level || x.size != y.size) return false;
      for(int ii = 0; ii < x.size; ++ii) {
        if(x.p[ii] != y.p[ii])
          return false;
      }
      return true;
    }
  };

  struct key_hash {
    size_t operator()(const key& x) const {
      uint32_t h(0);
      MurmurHash3_x86_32(x.p, x.size * sizeof(edge), (x.level<<5) + x.level + x.size, &h);
      return h; 
    }
  };

  node_id get_node(int level, vec<edge>& v) {
    key k { level, v.size(), v.begin() };
    auto it(table.find(k));
    if(it != table.end())
      return (*it).second;  

    // Otherwise, construct the node.
    int id(levels[level].size());
    levels[level].push(k);
    table.insert(std::make_pair(k, id));
    v.release();

    return id;
  }

  node_id build_node(int level, int* pb, int* pe) {
    // First, we sort the permutation by tuple-value.
    std::sort(pb, pe, [this, level](int i, int j) { return tuples[i][level] < tuples[j][level]; });
    vec<edge> children;
    if(level == tuples[0].size() - 1) {
      // Last level. Just add the (unique) edges directly
      int v = tuples[*pb][level];
      children.push(edge { v, 0 });
      for(++pb; pb != pe; ++pb) {
        if(tuples[*pb][level] == v)
          continue;
        v = tuples[*pb][level];
        children.push(edge { v, 0 });
      }
    } else {
      // Shouldn't be any duplicates at other levels, because
      // we're bundling them together at the recursive call.
      while(pb != pe) {
        int v(tuples[*pb][level]);
        // Collect the range corresponding to this value
        int* pm(pb);
        for(++pm; pm != pe; ++pm) {
          if(v < tuples[*pm][level])
            break;
        }
        children.push(edge { v, build_node(level+1, pb, pm) });
        pb = pm;
      }
    }
    
    return get_node(level, children);
  }

  struct flat_edge {
    int node;
    int val;
    node_id dest;
  };

  mdd_info* operator()(void) {
    vec<int> perm(tuples.size(), 0);
    for(int ii = 0; ii < perm.size(); ++ii)
      perm[ii] = ii;

    // Should only be one root.
    node_id r(build_node(0, perm.begin(), perm.end()));
    assert(r == 0);

    // Now build the mdd_info.
    mdd_info* m(new mdd_info());
    for(int ii = 0; ii < levels.size(); ++ii) {
      m->num_nodes.push(levels[ii].size());
      /*
      m->num_vals.push(1 + std::accumulate(levels[ii].begin(), levels[ii].end(),
        0, [](int s, key k) { return std::accumulate(k.begin(), k.end(), s, [](int s, edge e) { return std::max(s, e.val); }); }));
      */
      m->values.push();

      m->edge_HD.push();
      m->edge_TL.push();
      m->val_support.push();

      m->edge_value_id.push();
    }
    m->edge_TL.push();
    // True terminal
    m->num_nodes.push(1);

    // Allocate bit-vectors
    for(int ii = 0; ii < levels.size(); ++ii) {
      vec<key>& level(levels[ii]);  
      int ei = 0;
      vec< vec<int> > hd_supports(m->num_nodes[ii]);
      vec< vec<int> > tl_supports(m->num_nodes[ii+1]);
      vec< vec<int> > val_supports;

      // Construct the 
      vec<int> eperm;
      vec<flat_edge> flat;
      for(int ni = 0; ni < level.size(); ++ni) {
        for(edge e : level[ni]) {
          flat.push(flat_edge { ni, e.val, e.dest });
          eperm.push(eperm.size());
        }
      }
      m->num_edges.push(flat.size());

      std::sort(eperm.begin(), eperm.end(), [&flat](int e, int f) { return flat[e].val < flat[f].val; });

      int* b(eperm.begin());
      int* e(eperm.end());

      while(b != e) {
        int v = flat[*b].val;
        int v_id = m->values[ii].size();
         
        m->values[ii].push(v);
        val_supports.push();
        for(; b != e && flat[*b].val == v; ++b) {
          hd_supports[flat[*b].node].push(ei);
          tl_supports[flat[*b].dest].push(ei);
          val_supports[v_id].push(ei);
          m->edge_value_id[ii].push(v_id);
          ++ei;
        }
      }

      assert(ei == m->num_edges[ii]);
      for(const vec<int>& s : val_supports) {
        m->val_support[ii].push(btset::support_set::make(s));
      }
      for(const vec<int>& s : hd_supports) {
        m->edge_HD[ii].push(btset::support_set::make(s));
      }
      for(const vec<int>& s : tl_supports) {
        m->edge_TL[ii+1].push(btset::support_set::make(s));
      }
    }

    return m;
  }

  vec<int> tuple_perm;
  vec< vec<int> >& tuples;

  vec< vec<key> > levels;

  std::unordered_map<key, int, key_hash, key_eq> table;
};

mdd_id mdd_manager::build(vec< vec<int> >& tuples) {
  mdd_id mi(mdds.size());

  mddfier mddfy(tuples);

  /*
  mddfier::node_id n_id(mddfy()); 
  fprintf(stderr, "node id: %d\n", n_id);

  */
  mdd_info* m(mddfy());
  mdds.push(m);
          
  return mi;
}

mdd_id of_tuples(solver_data* s, vec< vec<int> >& tuples) {
  return mdd_manager::get(s)->build(tuples);
}
mdd_info& lookup(solver_data* s, mdd_id m) {
  return mdd_manager::get(s)->lookup(m);
}


  }
}
#if 0
// Assumes there are no skipped levels.
struct val_info {
  unsigned int var;
  int val;
};

struct mdd_info {
  size_t arity;
  size_t num_edges;

  vec< vec<int> > domains;
  vec< vec<support_set> > val_supports;

  vec< val_info > val_index;
};

using btset = btset::bitset;
using namespace bitset;

namespace geas {

class mdd_prop : public propagator, public prop_inst<mdd_prop> {
  // Parameters
  mdd_info& mdd;
  vec<intvar> xs;
  
  // Persistent state. Live edges and surviving values.
  btset live_edges;

  vec<p_sparseset> live_vals;

  p_sparseset killed_vals;

  static watch_result wake(void* ptr, int xi) {
    mdd_prop* p(static_cast<mdd_prop*>(ptr));
    p->changes.add(xi);
    p->queue_prop();
    return Wt_Keep;
  }

  public: 
    struct valpair { int var; intvar::val_t val; };

    mdd_prop(solver_data* s, mdd& _m, vec<intvar>& _vs)
      : propagator(s), vs(_vs) {
      
      int idx = 0;
      for(int ii : num_range(vs.size())) {
        intvar v(vs[ii]);
        for(intvar::val_t k : v.domain(s)) {
          attach(s, v != k, watch_callback(wake, this, idx));
          valpairs.push( valpair {ii, k} );
          idx++;
        }
      }
    }

    void root_simplify(void) {
      
    }
    
    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running mdd]]" << std::endl;
#endif

      return true;
    }

    // Persistent information
    vec<valpair> valpairs;
    vec<intvar> vs;

    // Transient data
    boolset changes;
};

}

#endif
