#ifndef GEAS__SOLVER_EXT__H
#define GEAS__SOLVER_EXT__H
#include <geas/solver/solver_data.h>
// For auto-magically registering
// solver extensions.
namespace geas {

template<class T>
class solver_ext {
  static man_id_t ext_id;

  static void* create(solver_data* s) { return static_cast<void*>(new T(s)); }
  static void destroy(void* v) { delete static_cast<T*>(v); }

public:
  static T* get(solver_data* s) { return static_cast<T*>(s->managers[ext_id].ptr); }
};
template<class T>
man_id_t solver_ext<T>::ext_id = register_manager(solver_ext<T>::create, solver_ext<T>::destroy);

template<class T>
class solver_ext_nofree {
  static man_id_t ext_id;

  static void* create(solver_data* s) { return static_cast<void*>(new T(s)); }
  static void destroy(void* v) { }

public:
  static T* get(solver_data* s) { return static_cast<T*>(s->managers[ext_id].ptr); }
};
template<class T>
man_id_t solver_ext_nofree<T>::ext_id = register_manager(solver_ext_nofree<T>::create, solver_ext_nofree<T>::destroy);


}

#endif
