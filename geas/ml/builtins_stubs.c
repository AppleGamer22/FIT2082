/* File generated from builtins.idl */

#include <stddef.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif
#include <caml/camlidlruntime.h>

#include <geas/c/builtins.h>
extern void camlidl_ml2c_atom_pred_t(value, pred_t *, camlidl_ctx _ctx);
extern value camlidl_c2ml_atom_pred_t(pred_t *, camlidl_ctx _ctx);

extern void camlidl_ml2c_atom_pval_t(value, pval_t *, camlidl_ctx _ctx);
extern value camlidl_c2ml_atom_pval_t(pval_t *, camlidl_ctx _ctx);

extern void camlidl_ml2c_atom_atom(value, atom *, camlidl_ctx _ctx);
extern value camlidl_c2ml_atom_atom(atom *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_result(value, result *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_result(result *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_var_choice(value, var_choice *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_var_choice(var_choice *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_val_choice(value, val_choice *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_val_choice(val_choice *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_statistics(value, statistics *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_statistics(statistics *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_options(value, options *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_options(options *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_limits(value, limits *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_limits(limits *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_solver(value, solver *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_solver(solver *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_model(value, model *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_model(model *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_intvar(value, intvar *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_intvar(intvar *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_intslice(value, intslice *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_intslice(intslice *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_fpvar(value, fpvar *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_fpvar(fpvar *, camlidl_ctx _ctx);

extern void camlidl_ml2c_solver_brancher(value, brancher *, camlidl_ctx _ctx);
extern value camlidl_c2ml_solver_brancher(brancher *, camlidl_ctx _ctx);

extern void camlidl_ml2c_internal_int_linterm(value, int_linterm *, camlidl_ctx _ctx);
extern value camlidl_c2ml_internal_int_linterm(int_linterm *, camlidl_ctx _ctx);

extern void camlidl_ml2c_internal_slice_linterm(value, slice_linterm *, camlidl_ctx _ctx);
extern value camlidl_c2ml_internal_slice_linterm(slice_linterm *, camlidl_ctx _ctx);

extern void camlidl_ml2c_internal_at_linterm(value, at_linterm *, camlidl_ctx _ctx);
extern value camlidl_c2ml_internal_at_linterm(at_linterm *, camlidl_ctx _ctx);

extern void camlidl_ml2c_internal_dtask(value, dtask *, camlidl_ctx _ctx);
extern value camlidl_c2ml_internal_dtask(dtask *, camlidl_ctx _ctx);

extern void camlidl_ml2c_internal_task(value, task *, camlidl_ctx _ctx);
extern value camlidl_c2ml_internal_task(task *, camlidl_ctx _ctx);

extern void camlidl_ml2c_internal_vtask(value, vtask *, camlidl_ctx _ctx);
extern value camlidl_c2ml_internal_vtask(vtask *, camlidl_ctx _ctx);

extern void camlidl_ml2c_internal_ftask(value, ftask *, camlidl_ctx _ctx);
extern value camlidl_c2ml_internal_ftask(ftask *, camlidl_ctx _ctx);

extern void camlidl_ml2c_internal_bp_flow(value, bp_flow *, camlidl_ctx _ctx);
extern value camlidl_c2ml_internal_bp_flow(bp_flow *, camlidl_ctx _ctx);

void camlidl_ml2c_builtins_task(value _v1, task * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
value _v5;
  _v3 = Field(_v1, 0);
  camlidl_ml2c_solver_intvar(_v3, &(*_c2).start, _ctx);
  _v4 = Field(_v1, 1);
  (*_c2).dur = Int_val(_v4);
  _v5 = Field(_v1, 2);
  (*_c2).res = Int_val(_v5);
}

value camlidl_c2ml_builtins_task(task * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[3];
  _v3[0] = _v3[1] = _v3[2] = 0;
  Begin_roots_block(_v3, 3)
    _v3[0] = camlidl_c2ml_solver_intvar(&(*_c2).start, _ctx);
    _v3[1] = Val_int((*_c2).dur);
    _v3[2] = Val_int((*_c2).res);
    _v1 = camlidl_alloc_small(3, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
    Field(_v1, 2) = _v3[2];
  End_roots()
  return _v1;
}

value camlidl_builtins_atmost_1(
	value _v_s,
	value _v_r,
	value _v_xs)
{
  solver s; /*in*/
  atom r; /*in*/
  atom *xs; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(atom ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_atom_atom(_v3, &xs[_c2], _ctx);
  }
  sz = _c1;
  _res = atmost_1(s, r, xs, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_atmost_k(
	value _v_s,
	value _v_r,
	value _v_xs,
	value _v_k)
{
  solver s; /*in*/
  atom r; /*in*/
  atom *xs; /*in*/
  int sz; /*in*/
  int k; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(atom ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_atom_atom(_v3, &xs[_c2], _ctx);
  }
  sz = _c1;
  k = Int_val(_v_k);
  _res = atmost_k(s, r, xs, sz, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_int_mul(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_x,
	value _v_y)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar x; /*in*/
  intvar y; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  camlidl_ml2c_solver_intvar(_v_y, &y, _ctx);
  _res = int_mul(s, r, z, x, y);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_int_div(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_x,
	value _v_y)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar x; /*in*/
  intvar y; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  camlidl_ml2c_solver_intvar(_v_y, &y, _ctx);
  _res = int_div(s, r, z, x, y);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_int_abs(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_x)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar x; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _res = int_abs(s, r, z, x);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_int_max(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_xs)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar *xs; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_solver_intvar(_v3, &xs[_c2], _ctx);
  }
  sz = _c1;
  _res = int_max(s, r, z, xs, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_int_le(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_x,
	value _v_k)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar x; /*in*/
  int k; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  k = Int_val(_v_k);
  _res = int_le(s, r, z, x, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_int_ne(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_x)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar x; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _res = int_ne(s, r, z, x);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_int_eq(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_x)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar x; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _res = int_eq(s, r, z, x);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_int_element(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_x,
	value _v_elts)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar x; /*in*/
  int *elts; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _c1 = Wosize_val(_v_elts);
  elts = camlidl_malloc(_c1 * sizeof(int ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_elts, _c2);
    elts[_c2] = Int_val(_v3);
  }
  sz = _c1;
  _res = int_element(s, r, z, x, elts, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_var_int_element(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_x,
	value _v_elts)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  intvar x; /*in*/
  intvar *elts; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_r, &r, _ctx);
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _c1 = Wosize_val(_v_elts);
  elts = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_elts, _c2);
    camlidl_ml2c_solver_intvar(_v3, &elts[_c2], _ctx);
  }
  sz = _c1;
  _res = var_int_element(s, r, z, x, elts, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_all_different_int(
	value _v_s,
	value _v_elts)
{
  solver s; /*in*/
  intvar *elts; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_elts);
  elts = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_elts, _c2);
    camlidl_ml2c_solver_intvar(_v3, &elts[_c2], _ctx);
  }
  sz = _c1;
  _res = all_different_int(s, elts, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_all_different_except_0(
	value _v_s,
	value _v_elts)
{
  solver s; /*in*/
  intvar *elts; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_elts);
  elts = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_elts, _c2);
    camlidl_ml2c_solver_intvar(_v3, &elts[_c2], _ctx);
  }
  sz = _c1;
  _res = all_different_except_0(s, elts, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_precede_chain_int(
	value _v_s,
	value _v_xs)
{
  solver s; /*in*/
  intvar *xs; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_solver_intvar(_v3, &xs[_c2], _ctx);
  }
  sz = _c1;
  _res = precede_chain_int(s, xs, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_precede_int(
	value _v_s,
	value _v_a,
	value _v_b,
	value _v_xs)
{
  solver s; /*in*/
  int a; /*in*/
  int b; /*in*/
  intvar *xs; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  a = Int_val(_v_a);
  b = Int_val(_v_b);
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_solver_intvar(_v3, &xs[_c2], _ctx);
  }
  sz = _c1;
  _res = precede_int(s, a, b, xs, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

int camlidl_transl_table_builtins_enum_17[4] = {
  Table_Clause,
  Table_Elem,
  Table_CT,
  Table_Default,
};

void camlidl_ml2c_builtins_table_mode(value _v1, table_mode * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_builtins_enum_17[Int_val(_v1)];
}

value camlidl_c2ml_builtins_table_mode(table_mode * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case Table_Clause: _v1 = Val_int(0); break;
  case Table_Elem: _v1 = Val_int(1); break;
  case Table_CT: _v1 = Val_int(2); break;
  case Table_Default: _v1 = Val_int(3); break;
  default: caml_invalid_argument("typedef table_mode: bad enum  value");
  }
  return _v1;
}

void camlidl_ml2c_builtins_table_id(value _v1, table_id * _c2, camlidl_ctx _ctx)
{
  (*_c2) = Int_val(_v1);
}

value camlidl_c2ml_builtins_table_id(table_id * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = Val_int((*_c2));
  return _v1;
}

value camlidl_builtins_build_table(
	value _v_s,
	value _v_arity,
	value _v_elts)
{
  solver s; /*in*/
  int arity; /*in*/
  int *elts; /*in*/
  int sz; /*in*/
  table_id _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  arity = Int_val(_v_arity);
  _c1 = Wosize_val(_v_elts);
  elts = camlidl_malloc(_c1 * sizeof(int ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_elts, _c2);
    elts[_c2] = Int_val(_v3);
  }
  sz = _c1;
  _res = build_table(s, arity, elts, sz);
  _vres = camlidl_c2ml_builtins_table_id(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_builtins_table(
	value _v_s,
	value _v_t,
	value _v_xs,
	value _v_m)
{
  solver s; /*in*/
  table_id t; /*in*/
  intvar *xs; /*in*/
  int sz; /*in*/
  table_mode m; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_builtins_table_id(_v_t, &t, _ctx);
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_solver_intvar(_v3, &xs[_c2], _ctx);
  }
  sz = _c1;
  camlidl_ml2c_builtins_table_mode(_v_m, &m, _ctx);
  _res = table(s, t, xs, sz, m);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

