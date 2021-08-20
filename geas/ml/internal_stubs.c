/* File generated from internal.idl */

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

void camlidl_ml2c_internal_int_linterm(value _v1, int_linterm * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
  _v3 = Field(_v1, 0);
  (*_c2).c = Int_val(_v3);
  _v4 = Field(_v1, 1);
  camlidl_ml2c_solver_intvar(_v4, &(*_c2).x, _ctx);
}

value camlidl_c2ml_internal_int_linterm(int_linterm * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[2];
  _v3[0] = _v3[1] = 0;
  Begin_roots_block(_v3, 2)
    _v3[0] = Val_int((*_c2).c);
    _v3[1] = camlidl_c2ml_solver_intvar(&(*_c2).x, _ctx);
    _v1 = camlidl_alloc_small(2, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
  End_roots()
  return _v1;
}

value camlidl_internal_linear_le(
	value _v_s,
	value _v_r,
	value _v_ts,
	value _v_k)
{
  solver s; /*in*/
  atom r; /*in*/
  int_linterm *ts; /*in*/
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
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(int_linterm ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_int_linterm(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  k = Int_val(_v_k);
  _res = linear_le(s, r, ts, sz, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_internal_linear_ne(
	value _v_s,
	value _v_r,
	value _v_ts,
	value _v_k)
{
  solver s; /*in*/
  atom r; /*in*/
  int_linterm *ts; /*in*/
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
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(int_linterm ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_int_linterm(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  k = Int_val(_v_k);
  _res = linear_ne(s, r, ts, sz, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

void camlidl_ml2c_internal_slice_linterm(value _v1, slice_linterm * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
  _v3 = Field(_v1, 0);
  (*_c2).c = Int_val(_v3);
  _v4 = Field(_v1, 1);
  camlidl_ml2c_solver_intslice(_v4, &(*_c2).x, _ctx);
}

value camlidl_c2ml_internal_slice_linterm(slice_linterm * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[2];
  _v3[0] = _v3[1] = 0;
  Begin_roots_block(_v3, 2)
    _v3[0] = Val_int((*_c2).c);
    _v3[1] = camlidl_c2ml_solver_intslice(&(*_c2).x, _ctx);
    _v1 = camlidl_alloc_small(2, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
  End_roots()
  return _v1;
}

value camlidl_internal_slice_linear_le(
	value _v_s,
	value _v_r,
	value _v_ts,
	value _v_k)
{
  solver s; /*in*/
  atom r; /*in*/
  slice_linterm *ts; /*in*/
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
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(slice_linterm ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_slice_linterm(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  k = Int_val(_v_k);
  _res = slice_linear_le(s, r, ts, sz, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

void camlidl_ml2c_internal_at_linterm(value _v1, at_linterm * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
  _v3 = Field(_v1, 0);
  (*_c2).c = Int_val(_v3);
  _v4 = Field(_v1, 1);
  camlidl_ml2c_atom_atom(_v4, &(*_c2).x, _ctx);
}

value camlidl_c2ml_internal_at_linterm(at_linterm * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[2];
  _v3[0] = _v3[1] = 0;
  Begin_roots_block(_v3, 2)
    _v3[0] = Val_int((*_c2).c);
    _v3[1] = camlidl_c2ml_atom_atom(&(*_c2).x, _ctx);
    _v1 = camlidl_alloc_small(2, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
  End_roots()
  return _v1;
}

value camlidl_internal_bool_linear_le(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_ts,
	value _v_k)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  at_linterm *ts; /*in*/
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
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(at_linterm ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_at_linterm(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  k = Int_val(_v_k);
  _res = bool_linear_le(s, r, z, ts, sz, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_internal_bool_linear_ge(
	value _v_s,
	value _v_r,
	value _v_z,
	value _v_ts,
	value _v_k)
{
  solver s; /*in*/
  atom r; /*in*/
  intvar z; /*in*/
  at_linterm *ts; /*in*/
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
  camlidl_ml2c_solver_intvar(_v_z, &z, _ctx);
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(at_linterm ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_at_linterm(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  k = Int_val(_v_k);
  _res = bool_linear_ge(s, r, z, ts, sz, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_internal_bool_linear_ne(
	value _v_s,
	value _v_r,
	value _v_ts,
	value _v_k)
{
  solver s; /*in*/
  atom r; /*in*/
  at_linterm *ts; /*in*/
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
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(at_linterm ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_at_linterm(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  k = Int_val(_v_k);
  _res = bool_linear_ne(s, r, ts, sz, k);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

void camlidl_ml2c_internal_dtask(value _v1, dtask * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
  _v3 = Field(_v1, 0);
  camlidl_ml2c_solver_intvar(_v3, &(*_c2).start, _ctx);
  _v4 = Field(_v1, 1);
  (*_c2).dur = Int_val(_v4);
}

value camlidl_c2ml_internal_dtask(dtask * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[2];
  _v3[0] = _v3[1] = 0;
  Begin_roots_block(_v3, 2)
    _v3[0] = camlidl_c2ml_solver_intvar(&(*_c2).start, _ctx);
    _v3[1] = Val_int((*_c2).dur);
    _v1 = camlidl_alloc_small(2, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
  End_roots()
  return _v1;
}

value camlidl_internal_disjunctive(
	value _v_s,
	value _v_ts)
{
  solver s; /*in*/
  dtask *ts; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(dtask ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_dtask(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  _res = disjunctive(s, ts, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

void camlidl_ml2c_internal_task(value _v1, task * _c2, camlidl_ctx _ctx)
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

value camlidl_c2ml_internal_task(task * _c2, camlidl_ctx _ctx)
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

void camlidl_ml2c_internal_vtask(value _v1, vtask * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
value _v5;
  _v3 = Field(_v1, 0);
  camlidl_ml2c_solver_intvar(_v3, &(*_c2).start, _ctx);
  _v4 = Field(_v1, 1);
  camlidl_ml2c_solver_intvar(_v4, &(*_c2).dur, _ctx);
  _v5 = Field(_v1, 2);
  camlidl_ml2c_solver_intvar(_v5, &(*_c2).res, _ctx);
}

value camlidl_c2ml_internal_vtask(vtask * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[3];
  _v3[0] = _v3[1] = _v3[2] = 0;
  Begin_roots_block(_v3, 3)
    _v3[0] = camlidl_c2ml_solver_intvar(&(*_c2).start, _ctx);
    _v3[1] = camlidl_c2ml_solver_intvar(&(*_c2).dur, _ctx);
    _v3[2] = camlidl_c2ml_solver_intvar(&(*_c2).res, _ctx);
    _v1 = camlidl_alloc_small(3, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
    Field(_v1, 2) = _v3[2];
  End_roots()
  return _v1;
}

void camlidl_ml2c_internal_ftask(value _v1, ftask * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
value _v5;
  _v3 = Field(_v1, 0);
  camlidl_ml2c_solver_intvar(_v3, &(*_c2).start, _ctx);
  _v4 = Field(_v1, 1);
  (*_c2).dur = Int_val(_v4);
  _v5 = Field(_v1, 2);
  (*_c2).res = Double_val(_v5);
}

value camlidl_c2ml_internal_ftask(ftask * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[3];
  _v3[0] = _v3[1] = _v3[2] = 0;
  Begin_roots_block(_v3, 3)
    _v3[0] = camlidl_c2ml_solver_intvar(&(*_c2).start, _ctx);
    _v3[1] = Val_int((*_c2).dur);
    _v3[2] = caml_copy_double((*_c2).res);
    _v1 = camlidl_alloc_small(3, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
    Field(_v1, 2) = _v3[2];
  End_roots()
  return _v1;
}

value camlidl_internal_cumulative(
	value _v_s,
	value _v_ts,
	value _v_cap)
{
  solver s; /*in*/
  task *ts; /*in*/
  int sz; /*in*/
  int cap; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(task ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_task(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  cap = Int_val(_v_cap);
  _res = cumulative(s, ts, sz, cap);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_internal_cumulative_var(
	value _v_s,
	value _v_ts,
	value _v_cap)
{
  solver s; /*in*/
  vtask *ts; /*in*/
  int sz; /*in*/
  intvar cap; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(vtask ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_vtask(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  camlidl_ml2c_solver_intvar(_v_cap, &cap, _ctx);
  _res = cumulative_var(s, ts, sz, cap);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_internal_cumulative_float(
	value _v_s,
	value _v_ts,
	value _v_cap)
{
  solver s; /*in*/
  ftask *ts; /*in*/
  int sz; /*in*/
  float cap; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_ts);
  ts = camlidl_malloc(_c1 * sizeof(ftask ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_ts, _c2);
    camlidl_ml2c_internal_ftask(_v3, &ts[_c2], _ctx);
  }
  sz = _c1;
  cap = Double_val(_v_cap);
  _res = cumulative_float(s, ts, sz, cap);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

void camlidl_ml2c_internal_bp_flow(value _v1, bp_flow * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
value _v5;
  _v3 = Field(_v1, 0);
  camlidl_ml2c_atom_atom(_v3, &(*_c2).at, _ctx);
  _v4 = Field(_v1, 1);
  (*_c2).src = Int_val(_v4);
  _v5 = Field(_v1, 2);
  (*_c2).sink = Int_val(_v5);
}

value camlidl_c2ml_internal_bp_flow(bp_flow * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[3];
  _v3[0] = _v3[1] = _v3[2] = 0;
  Begin_roots_block(_v3, 3)
    _v3[0] = camlidl_c2ml_atom_atom(&(*_c2).at, _ctx);
    _v3[1] = Val_int((*_c2).src);
    _v3[2] = Val_int((*_c2).sink);
    _v1 = camlidl_alloc_small(3, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
    Field(_v1, 2) = _v3[2];
  End_roots()
  return _v1;
}

value camlidl_internal_bipartite_flow(
	value _v_s,
	value _v_srcs,
	value _v_sinks,
	value _v_flows)
{
  solver s; /*in*/
  int *srcs; /*in*/
  int srcs_sz; /*in*/
  int *sinks; /*in*/
  int sinks_sz; /*in*/
  bp_flow *flows; /*in*/
  int flows_sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  mlsize_t _c7;
  mlsize_t _c8;
  value _v9;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_srcs);
  srcs = camlidl_malloc(_c1 * sizeof(int ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_srcs, _c2);
    srcs[_c2] = Int_val(_v3);
  }
  srcs_sz = _c1;
  _c4 = Wosize_val(_v_sinks);
  sinks = camlidl_malloc(_c4 * sizeof(int ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_sinks, _c5);
    sinks[_c5] = Int_val(_v6);
  }
  sinks_sz = _c4;
  _c7 = Wosize_val(_v_flows);
  flows = camlidl_malloc(_c7 * sizeof(bp_flow ), _ctx);
  for (_c8 = 0; _c8 < _c7; _c8++) {
    _v9 = Field(_v_flows, _c8);
    camlidl_ml2c_internal_bp_flow(_v9, &flows[_c8], _ctx);
  }
  flows_sz = _c7;
  _res = bipartite_flow(s, srcs, srcs_sz, sinks, sinks_sz, flows, flows_sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

