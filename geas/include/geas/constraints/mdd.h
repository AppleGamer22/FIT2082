#ifndef GEAS__MDD_H
#define GEAS__MDD_H
#include <geas/solver/solver_data.h>
#include <geas/utils/bitset.h>

// Packed-bit representation of MDDs.
namespace geas {
  namespace mdd {

// TODO: Condense the MDD value sets.
struct mdd_info {
  mdd_info(void) { }

  vec<unsigned int> num_nodes;
  vec<unsigned int> num_edges;
  vec< vec<int> > values;

  vec< vec<btset::support_set> > val_support;
  vec< vec<btset::support_set> > edge_HD;
  vec< vec<btset::support_set> > edge_TL;

  vec< vec<int> > edge_value_id;
};

typedef int mdd_id;

mdd_id of_tuples(solver_data* s, vec< vec<int> >& tuples);
mdd_info& lookup(solver_data* s, mdd_id m);


  }
}
#endif
