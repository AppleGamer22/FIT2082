#ifndef GEAS_C_MARSHAL_H
#define GEAS_C_MARSHAL_H
#include <geas/solver/solver.h>
#include <geas/solver/model.h>
#include <geas/c/atom.h>
#include <geas/c/geas.h>
#include <geas/vars/slice.h>

inline geas::solver* get_solver(solver s) {
  return (geas::solver*) s;
}
inline geas::intvar* get_intvar(intvar v) {
  return (geas::intvar*) v;
}
inline geas::int_slice* get_intslice(intslice v) {
  return (geas::int_slice*) v;
}
inline geas::fp::fpvar* get_fpvar(fpvar v) {
  return (geas::fp::fpvar*) v;
}
inline geas::patom_t get_atom(atom at) {
  return geas::patom_t(at.pid, at.val);
}
inline atom unget_atom(geas::patom_t at) {
  atom a = { at.pid, at.val };
  return a;
}

inline geas::model* get_model(model m) {
  return (geas::model*) m;
}

inline geas::brancher* get_brancher(brancher b) {
  return (geas::brancher*) b;
}

inline result unget_result(geas::solver::result r) {
  switch(r) {
    case geas::solver::SAT:
      return SAT;
    case geas::solver::UNSAT:
      return UNSAT;
    case geas::solver::UNKNOWN:
    default:
      return UNKNOWN;
  }
}

#endif
