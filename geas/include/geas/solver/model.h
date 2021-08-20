#ifndef GEAS_MODEL_H
#define GEAS_MODEL_H
#include <geas/mtl/Vec.h>
#include <geas/engine/geas-types.h>

namespace geas {

struct model {
  model(void) { };

  pval_t get(pid_t pi) const {
    if(pi&1) {
      return pval_inv(vals[pi>>1]);
    } else {
      return vals[pi>>1];
    }
  }

  template<class T>
  typename T::val_t operator[](const T& v) {
    return v.model_val(*this);
  }

  bool value(patom_t at) const {
    if(at.pid&1) {
      return vals[at.pid>>1] < pval_contra(at.val);
    } else {
      return vals[at.pid>>1] >= at.val;
    }
  }

  vec<pval_t> vals;
};

}

#endif
