#ifndef GEAS_C_BUILTINS_H
#define GEAS_C_BUILTINS_H
#include <geas/c/atom.h>
#include <geas/c/geas.h>

#ifdef __cplusplus
extern "C" {
#endif

/* These return false on top-level failure. */
// int clause(solver s, atom* cl, int sz);

typedef struct {
  int c;
  intvar x; 
} int_linterm;

// These are half-reified.
// For strict versions, call with r = at_True
int linear_le(solver s, atom r, int_linterm* ts, int sz, int k);
int linear_ne(solver s, atom r, int_linterm* ts, int sz, int k);

typedef struct {
  int c;
  intslice x; 
} slice_linterm;

typedef struct {
  int c;
  atom x;
} at_linterm;

int slice_linear_le(solver s, atom r, slice_linterm* ts, int sz, int k);

// int bool_linear_le(solver s, atom r, at_linterm* ts, int sz, int k);
int bool_linear_le(solver s, atom, intvar, at_linterm* ts, int sz, int k);
int bool_linear_ge(solver s, atom, intvar, at_linterm* ts, int sz, int k);
int bool_linear_ne(solver s, atom r, at_linterm* ts, int sz, int k);
int atmost_1(solver s, atom r, atom* xs, int sz);
int atmost_k(solver s, atom r, atom* xs, int sz, int k);

// r -> (x <= y + k)
int int_le(solver s, atom r, intvar x, intvar y, int k);
int int_ne(solver s, atom r, intvar x, intvar y);
int int_eq(solver s, atom r, intvar x, intvar y);

int int_mul(solver s, atom r, intvar z, intvar x, intvar y);
int int_div(solver s, atom r, intvar z, intvar x, intvar y);
int int_abs(solver s, atom r, intvar z, intvar x);

int int_max(solver s, atom r, intvar z, intvar* xs, int sz);

int int_element(solver s, atom r, intvar z, intvar i, int* elts, int sz);
int var_int_element(solver s, atom r, intvar z, intvar i, intvar* elts, int sz);

int all_different_int(solver s, intvar* xs, int sz);
int all_different_except_0(solver s, intvar* xs, int sz);

typedef struct { intvar start; int dur; int res; } task;
int cumulative(solver s, task* ts, int sz, int cap);

typedef struct { intvar start; intvar dur; intvar res; } vtask;
int cumulative_var(solver s, vtask* ts, int sz, intvar cap);

typedef struct { intvar start; int dur; float res; } ftask;
int cumulative_float(solver s, ftask* ts, int sz, float cap);

typedef struct { intvar start; int dur; } dtask;
int disjunctive(solver s, dtask* ts, int sz);

typedef struct { atom at; int src; int sink; } bp_flow;
int bipartite_flow(solver s, int* srcs, int srcs_sz, int* sinks, int sinks_sz, bp_flow* flows, int flows_sz);

// Restricted form of int-value-precede-chain.
int precede_int(solver s, int a, int b, intvar* xs, int sz);
int precede_chain_int(solver s, intvar* xs, int sz);
int values_precede_chain_int(solver s, int* vs, int vs_sz,
  intvar* xs, int xs_sz);

// Tables
typedef enum { Table_Clause, Table_Elem, Table_CT, Table_Default } table_mode;
typedef int table_id;
table_id build_table(solver s, int arity, int* elts, int sz);
int table(solver s, table_id t, intvar* xs, int sz, table_mode m);

// Regular
// typedef int reg_id;
// reg_id build_regular(solver s, int num_states, 
#ifdef __cplusplus
}
#endif

#endif
