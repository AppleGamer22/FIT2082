#ifndef GEAS_BUILTINS_H
#define GEAS_BUILTINS_H
#include <geas/vars/intvar.h>

namespace geas {
// linear.cc
bool linear_le(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r = at_True);
bool linear_ne(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r = at_True);
// linear-ps.cc
bool linear_le_ps(solver_data* s, vec<int>& ks, vec<intvar>& vs, int k,
  patom_t r = at_True);

// bool-linear.cc
bool atmost_1(solver_data*, vec<patom_t>& xs, patom_t r = at_True);
bool atmost_k(solver_data*, vec<patom_t>& xs, int k, patom_t r = at_True);
bool bool_linear_le(solver_data* s, patom_t r, intvar z, vec<int>& ks, vec<patom_t>& xs, int k);
bool bool_linear_ge(solver_data* s, patom_t r, intvar z, vec<int>& ks, vec<patom_t>& xs, int k);
bool bool_linear_ge(solver_data* s, patom_t r, int c_z, intvar z, vec<int>& ks, vec<patom_t>& xs, int k);
bool bool_linear_ne(solver_data* s, vec<int>& ks, vec<patom_t>& xs, int k, patom_t r = at_True);

// element.cc
bool int_element(solver_data* s, intvar x, intvar i, vec<int>& ys,
  patom_t r = at_True);
bool var_int_element(solver_data* s, intvar x, intvar i, vec<intvar>& ys,
  patom_t r = at_True);

// disjunctive.cc
bool disjunctive_int(solver_data* s, vec<intvar>& st, vec<int>& du); 
bool disjunctive_var(solver_data* s, vec<intvar>& st, vec<intvar>& du);

// cumulative.cc
bool cumulative(solver_data* s,
  vec<intvar>& starts, vec<int>& durations, vec<int>& resources, int cap);
bool cumulative_sel(solver_data* s,
  vec<intvar>& starts, vec<intvar>& durations, vec<int>& resources, vec<patom_t>& sel, int cap);
bool cumulative_var(solver_data* s,
  vec<intvar>& starts, vec<intvar>& durations, vec<intvar>& resources, intvar cap);
bool cumulative_float(solver_data* s,
  vec<intvar>& starts, vec<int>& durations, vec<float>& resources, float cap);

// arith.cc
bool int_max(solver_data* s, intvar z, vec<intvar>& xs, patom_t r = at_True);
bool int_abs(solver_data* s, intvar z, intvar x, patom_t r = at_True);
bool int_mul(solver_data* s, intvar z, intvar x, intvar y, patom_t r = at_True);
bool int_div(solver_data* s, intvar z, intvar x, intvar y, patom_t r = at_True);

// x <= y + k
// bool int_le(solver_data* s, intvar x, intvar y, intvar::val_t k);

// r -> (x <= y)
bool pred_le(solver_data* s, pid_t x, pid_t y, int k, patom_t r = at_True);
bool int_le(solver_data* s, intvar x, intvar y, int k, patom_t r = at_True);
bool int_ne(solver_data* s, intvar x, intvar y, patom_t r = at_True);
bool int_eq(solver_data* s, intvar x, intvar y, patom_t r = at_True);

// alldifferent.cc
bool all_different_int(solver_data* s, const vec<intvar>& xs, patom_t r = at_True);
bool all_different_except_0(solver_data* s, const vec<intvar>& xs, patom_t r = at_True);

// values-precede.cc
bool int_precede_chain(solver_data* s, vec<intvar>& xs, patom_t r = at_True);
bool int_value_precede(solver_data* s, int pre, int post, vec<intvar>& xs);

// table.cc
typedef int table_id;
namespace table {
  enum TableMode { Table_Clause, Table_Elem, Table_CT, Table_Default };
  table_id build(solver_data* s, vec< vec<int> >& rows);
  bool post(solver_data* s, table_id t, vec<intvar>& xs, TableMode mode = Table_Default);
}

}
#endif
