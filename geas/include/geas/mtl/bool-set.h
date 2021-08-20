#ifndef GEAS_BOOL_SET_H
#define GEAS_BOOL_SET_H
#include <geas/mtl/Vec.h>

// A monotone set for collecting changes.
class boolset {
public:
  boolset(void) { }
  boolset(int sz) {
    growTo(sz);
  }

  void growTo(int sz) {
    is_touched.growTo(sz, false);
  }

  void add(int k) {
    if(!is_touched[k]) {
      touched.push(k);
      is_touched[k] = true;
    }
  }

  void hide(int k) {
    is_touched[k] = true;
  }

  bool elem(int k) const { return is_touched[k]; }
  void clear(void) {
    for(int t : touched) {
      is_touched[t] = false;
    }
    touched.clear();
  }

  int size(void) const { return touched.size(); }
  int cap(void) const { return is_touched.size(); }

  int* begin(void) { return touched.begin(); }
  int* end(void) { return touched.end(); }

protected:
  vec<bool> is_touched;
  vec<int> touched;
};

#endif
