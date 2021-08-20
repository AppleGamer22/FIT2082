#ifndef GEAS__PROPAGATOR_EXT_H
#define GEAS__PROPAGATOR_EXT_H
// Header file for syntactic-sugar templated
// function definitions
#include <geas/solver/solver_data.h>
namespace geas {

template<class T>
inline void propagator::set(trailed<T>& x, T k) {
  x.set(s->persist, k);
}

template<class T>
inline void propagator::save(T& t, char& flag) {
  trail_save(s->persist, t, flag);
}

template<class T> bool propagator::is_fixed(const T& v) const {
  return v.is_fixed(s->state.p_vals);
}

template<class T>
auto propagator::lb(const T& v) const -> decltype(v.lb(((pred_state*) nullptr)->p_vals)) {
  return v.lb(s->state.p_vals); 
};
template<class T>
auto propagator::ub(const T& v) const -> decltype(v.ub(((pred_state*) nullptr)->p_vals)) {
  return v.ub(s->state.p_vals);
}
template<class T>
auto propagator::lb_0(const T& v) const -> decltype(v.lb(((pred_state*) nullptr)->p_root)) {
  return v.lb(s->state.p_root);
}
template<class T>
auto propagator::ub_0(const T& v) const -> decltype(v.ub(((pred_state*) nullptr)->p_root)) {
  return v.ub(s->state.p_root);
}

template<class T>
auto propagator::lb_prev(const T& v) const -> decltype(v.lb(((pred_state*) nullptr)->p_last)) {
  return v.lb(s->state.p_last);
}
template<class T> typename T::val_t propagator::lb_delta(const T& v) const {
  return v.lb_delta(s->state.p_vals, s->wake_vals);
}
template<class T> typename T::val_t propagator::ub_delta(const T& v) const {
  return v.ub_delta(s->state.p_vals, s->wake_vals);
}
template<class T>
auto propagator::ub_prev(const T& v) const -> decltype(v.ub(((pred_state*) nullptr)->p_last)) {
  return v.ub(s->state.p_last);
}
template<class T> bool propagator::in_domain(const T& v, typename T::val_t k) const {
  return v.in_domain(s->state.p_vals, k);
}
template<class T, class V> bool propagator::set_lb(T& x, V v, reason r) {
  return enqueue(*s, x >= v, r); 
}
template<class T, class V> bool propagator::set_ub(T& x, V v, reason r) {
  return enqueue(*s, x <= v, r);
}
template<class T> bool propagator::set_lb_with_eq(T& x, typename T::val_t v, reason r) {
  typename T::val_t l(x.lb(s));
  if(l >= v)
    return true;
  return enqueue(*s, x >= v, r) && x.enforce_eqatoms_lb(l); 
}
template<class T> bool propagator::set_ub_with_eq(T& x, typename T::val_t v, reason r) {
  typename T::val_t u(x.ub(s));
  if(u <= v)
    return true;
  return enqueue(*s, x <= v, r) && x.enforce_eqatoms_ub(u);
}
template<class T> void propagator::EX_PUSH(T& expl, patom_t at) {
  assert(!ub(at));
  expl.push(at);
}
}

#endif
