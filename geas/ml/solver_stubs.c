/* File generated from solver.idl */

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

#include <geas/solver/stats.h>
#include <geas/solver/options.h>
#include <geas/c/geas.h>
extern void camlidl_ml2c_atom_pred_t(value, pred_t *, camlidl_ctx _ctx);
extern value camlidl_c2ml_atom_pred_t(pred_t *, camlidl_ctx _ctx);

extern void camlidl_ml2c_atom_pval_t(value, pval_t *, camlidl_ctx _ctx);
extern value camlidl_c2ml_atom_pval_t(pval_t *, camlidl_ctx _ctx);

extern void camlidl_ml2c_atom_atom(value, atom *, camlidl_ctx _ctx);
extern value camlidl_c2ml_atom_atom(atom *, camlidl_ctx _ctx);

void free_solver(solver* s) { destroy_solver(*s); }
void free_model(model* m) { destroy_model(*m); }
void free_intvar(intvar* v) { destroy_intvar(*v); }
void free_floatvar(fpvar* v) { destroy_floatvar(*v); }
void free_intslice(intslice* v) { destroy_intslice(*v); }
int cmp_intvar(intvar* x, intvar* y) { return compare_intvar(*x, *y); }
int hsh_intvar(intvar* x) { return hash_intvar(*x); }
int cmp_intslice(intslice* x, intslice* y) { return compare_intslice(*x, *y); }
int hsh_intslice(intslice* x) { return hash_intslice(*x); }
int camlidl_transl_table_solver_enum_2[3] = {
  SAT,
  UNSAT,
  UNKNOWN,
};

void camlidl_ml2c_solver_result(value _v1, result * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_solver_enum_2[Int_val(_v1)];
}

value camlidl_c2ml_solver_result(result * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case SAT: _v1 = Val_int(0); break;
  case UNSAT: _v1 = Val_int(1); break;
  case UNKNOWN: _v1 = Val_int(2); break;
  default: caml_invalid_argument("typedef result: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_solver_enum_3[4] = {
  VAR_INORDER,
  VAR_FIRSTFAIL,
  VAR_LEAST,
  VAR_GREATEST,
};

void camlidl_ml2c_solver_var_choice(value _v1, var_choice * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_solver_enum_3[Int_val(_v1)];
}

value camlidl_c2ml_solver_var_choice(var_choice * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case VAR_INORDER: _v1 = Val_int(0); break;
  case VAR_FIRSTFAIL: _v1 = Val_int(1); break;
  case VAR_LEAST: _v1 = Val_int(2); break;
  case VAR_GREATEST: _v1 = Val_int(3); break;
  default: caml_invalid_argument("typedef var_choice: bad enum  value");
  }
  return _v1;
}

int camlidl_transl_table_solver_enum_4[3] = {
  VAL_MIN,
  VAL_MAX,
  VAL_SPLIT,
};

void camlidl_ml2c_solver_val_choice(value _v1, val_choice * _c2, camlidl_ctx _ctx)
{
  (*_c2) = camlidl_transl_table_solver_enum_4[Int_val(_v1)];
}

value camlidl_c2ml_solver_val_choice(val_choice * _c2, camlidl_ctx _ctx)
{
value _v1;
  switch((*_c2)) {
  case VAL_MIN: _v1 = Val_int(0); break;
  case VAL_MAX: _v1 = Val_int(1); break;
  case VAL_SPLIT: _v1 = Val_int(2); break;
  default: caml_invalid_argument("typedef val_choice: bad enum  value");
  }
  return _v1;
}

void camlidl_ml2c_solver_statistics(value _v1, statistics * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
value _v5;
value _v6;
value _v7;
value _v8;
  _v3 = Field(_v1, 0);
  (*_c2).conflicts = Int_val(_v3);
  _v4 = Field(_v1, 1);
  (*_c2).restarts = Int_val(_v4);
  _v5 = Field(_v1, 2);
  (*_c2).solutions = Int_val(_v5);
  _v6 = Field(_v1, 3);
  (*_c2).time = Double_val(_v6);
  _v7 = Field(_v1, 4);
  (*_c2).num_learnts = Int_val(_v7);
  _v8 = Field(_v1, 5);
  (*_c2).num_learnt_lits = Int_val(_v8);
}

value camlidl_c2ml_solver_statistics(statistics * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[6];
  memset(_v3, 0, 6 * sizeof(value));
  Begin_roots_block(_v3, 6)
    _v3[0] = Val_int((*_c2).conflicts);
    _v3[1] = Val_int((*_c2).restarts);
    _v3[2] = Val_int((*_c2).solutions);
    _v3[3] = caml_copy_double((*_c2).time);
    _v3[4] = Val_int((*_c2).num_learnts);
    _v3[5] = Val_int((*_c2).num_learnt_lits);
    _v1 = camlidl_alloc_small(6, 0);
    { mlsize_t _c4;
      for (_c4 = 0; _c4 < 6; _c4++) Field(_v1, _c4) = _v3[_c4];
    }
  End_roots()
  return _v1;
}

void camlidl_ml2c_solver_options(value _v1, options * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
value _v5;
value _v6;
value _v7;
value _v8;
value _v9;
value _v10;
value _v11;
value _v12;
value _v13;
  _v3 = Field(_v1, 0);
  (*_c2).learnt_dbmax = Int_val(_v3);
  _v4 = Field(_v1, 1);
  (*_c2).learnt_growthrate = Double_val(_v4);
  _v5 = Field(_v1, 2);
  (*_c2).pred_act_inc = Double_val(_v5);
  _v6 = Field(_v1, 3);
  (*_c2).pred_act_growthrate = Double_val(_v6);
  _v7 = Field(_v1, 4);
  (*_c2).learnt_act_inc = Double_val(_v7);
  _v8 = Field(_v1, 5);
  (*_c2).learnt_act_growthrate = Double_val(_v8);
  _v9 = Field(_v1, 6);
  (*_c2).restart_limit = Int_val(_v9);
  _v10 = Field(_v1, 7);
  (*_c2).restart_growthrate = Double_val(_v10);
  _v11 = Field(_v1, 8);
  (*_c2).one_watch = Int_val(_v11);
  _v12 = Field(_v1, 9);
  (*_c2).global_diff = Int_val(_v12);
  _v13 = Field(_v1, 10);
  (*_c2).eager_threshold = Int_val(_v13);
}

value camlidl_c2ml_solver_options(options * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[11];
  memset(_v3, 0, 11 * sizeof(value));
  Begin_roots_block(_v3, 11)
    _v3[0] = Val_int((*_c2).learnt_dbmax);
    _v3[1] = caml_copy_double((*_c2).learnt_growthrate);
    _v3[2] = caml_copy_double((*_c2).pred_act_inc);
    _v3[3] = caml_copy_double((*_c2).pred_act_growthrate);
    _v3[4] = caml_copy_double((*_c2).learnt_act_inc);
    _v3[5] = caml_copy_double((*_c2).learnt_act_growthrate);
    _v3[6] = Val_int((*_c2).restart_limit);
    _v3[7] = caml_copy_double((*_c2).restart_growthrate);
    _v3[8] = Val_int((*_c2).one_watch);
    _v3[9] = Val_int((*_c2).global_diff);
    _v3[10] = Val_int((*_c2).eager_threshold);
    _v1 = camlidl_alloc_small(11, 0);
    { mlsize_t _c4;
      for (_c4 = 0; _c4 < 11; _c4++) Field(_v1, _c4) = _v3[_c4];
    }
  End_roots()
  return _v1;
}

void camlidl_ml2c_solver_limits(value _v1, limits * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
  _v3 = Field(_v1, 0);
  (*_c2).time = Double_val(_v3);
  _v4 = Field(_v1, 1);
  (*_c2).conflicts = Int_val(_v4);
}

value camlidl_c2ml_solver_limits(limits * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[2];
  _v3[0] = _v3[1] = 0;
  Begin_roots_block(_v3, 2)
    _v3[0] = caml_copy_double((*_c2).time);
    _v3[1] = Val_int((*_c2).conflicts);
    _v1 = camlidl_alloc_small(2, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
  End_roots()
  return _v1;
}

void camlidl_ml2c_solver_solver(value _v1, solver * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((solver *) Data_custom_val(_v1));
}

static void camlidl_finalize_solver_solver(value v)
{
  free_solver((solver *) Data_custom_val(v));
}
struct custom_operations camlidl_cops_solver_solver = {
  NULL,
  camlidl_finalize_solver_solver,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

value camlidl_c2ml_solver_solver(solver * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = caml_alloc_custom(&camlidl_cops_solver_solver, sizeof(solver), 0, 1);
  *((solver *) Data_custom_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_solver_model(value _v1, model * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((model *) Data_custom_val(_v1));
}

static void camlidl_finalize_solver_model(value v)
{
  free_model((model *) Data_custom_val(v));
}
struct custom_operations camlidl_cops_solver_model = {
  NULL,
  camlidl_finalize_solver_model,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

value camlidl_c2ml_solver_model(model * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = caml_alloc_custom(&camlidl_cops_solver_model, sizeof(model), 0, 1);
  *((model *) Data_custom_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_solver_intvar(value _v1, intvar * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((intvar *) Data_custom_val(_v1));
}

static void camlidl_finalize_solver_intvar(value v)
{
  free_intvar((intvar *) Data_custom_val(v));
}
static int camlidl_compare_solver_intvar(value v1, value v2)
{
  return cmp_intvar((intvar *) Data_custom_val(v1), (intvar *) Data_custom_val(v2));
}
static long camlidl_hash_solver_intvar(value v)
{
  return hsh_intvar((intvar *) Data_custom_val(v));
}
struct custom_operations camlidl_cops_solver_intvar = {
  NULL,
  camlidl_finalize_solver_intvar,
  camlidl_compare_solver_intvar,
  camlidl_hash_solver_intvar,
  custom_serialize_default,
  custom_deserialize_default
};

value camlidl_c2ml_solver_intvar(intvar * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = caml_alloc_custom(&camlidl_cops_solver_intvar, sizeof(intvar), 0, 1);
  *((intvar *) Data_custom_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_solver_intslice(value _v1, intslice * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((intslice *) Data_custom_val(_v1));
}

static void camlidl_finalize_solver_intslice(value v)
{
  free_intslice((intslice *) Data_custom_val(v));
}
static int camlidl_compare_solver_intslice(value v1, value v2)
{
  return cmp_intslice((intslice *) Data_custom_val(v1), (intslice *) Data_custom_val(v2));
}
static long camlidl_hash_solver_intslice(value v)
{
  return hsh_intslice((intslice *) Data_custom_val(v));
}
struct custom_operations camlidl_cops_solver_intslice = {
  NULL,
  camlidl_finalize_solver_intslice,
  camlidl_compare_solver_intslice,
  camlidl_hash_solver_intslice,
  custom_serialize_default,
  custom_deserialize_default
};

value camlidl_c2ml_solver_intslice(intslice * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = caml_alloc_custom(&camlidl_cops_solver_intslice, sizeof(intslice), 0, 1);
  *((intslice *) Data_custom_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_solver_fpvar(value _v1, fpvar * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((fpvar *) Data_custom_val(_v1));
}

static void camlidl_finalize_solver_fpvar(value v)
{
  free_floatvar((fpvar *) Data_custom_val(v));
}
struct custom_operations camlidl_cops_solver_fpvar = {
  NULL,
  camlidl_finalize_solver_fpvar,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

value camlidl_c2ml_solver_fpvar(fpvar * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = caml_alloc_custom(&camlidl_cops_solver_fpvar, sizeof(fpvar), 0, 1);
  *((fpvar *) Data_custom_val(_v1)) = *_c2;
  return _v1;
}

void camlidl_ml2c_solver_brancher(value _v1, brancher * _c2, camlidl_ctx _ctx)
{
  *_c2 = *((brancher *) Bp_val(_v1));
}

value camlidl_c2ml_solver_brancher(brancher * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = camlidl_alloc((sizeof(brancher) + sizeof(value) - 1) / sizeof(value), Abstract_tag);
  *((brancher *) Bp_val(_v1)) = *_c2;
  return _v1;
}

value camlidl_solver_default_opts(value _unit)
{
  options _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _res = default_opts();
  _vres = camlidl_c2ml_solver_options(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_new_solver(
	value _v_o)
{
  options o; /*in*/
  solver _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_options(_v_o, &o, _ctx);
  _res = new_solver(o);
  _vres = camlidl_c2ml_solver_solver(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_solver_id(
	value _v_s)
{
  solver s; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _res = solver_id(s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_new_int_brancher(
	value _v_varc,
	value _v_valc,
	value _v_vs)
{
  var_choice varc; /*in*/
  val_choice valc; /*in*/
  intvar *vs; /*in*/
  int sz; /*in*/
  brancher _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_var_choice(_v_varc, &varc, _ctx);
  camlidl_ml2c_solver_val_choice(_v_valc, &valc, _ctx);
  _c1 = Wosize_val(_v_vs);
  vs = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_vs, _c2);
    camlidl_ml2c_solver_intvar(_v3, &vs[_c2], _ctx);
  }
  sz = _c1;
  _res = new_int_brancher(varc, valc, vs, sz);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_new_bool_brancher(
	value _v_varc,
	value _v_valc,
	value _v_vs)
{
  var_choice varc; /*in*/
  val_choice valc; /*in*/
  atom *vs; /*in*/
  int sz; /*in*/
  brancher _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_var_choice(_v_varc, &varc, _ctx);
  camlidl_ml2c_solver_val_choice(_v_valc, &valc, _ctx);
  _c1 = Wosize_val(_v_vs);
  vs = camlidl_malloc(_c1 * sizeof(atom ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_vs, _c2);
    camlidl_ml2c_atom_atom(_v3, &vs[_c2], _ctx);
  }
  sz = _c1;
  _res = new_bool_brancher(varc, valc, vs, sz);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_new_bool_priority_brancher(
	value _v_varc,
	value _v_xs,
	value _v_bs)
{
  var_choice varc; /*in*/
  atom *xs; /*in*/
  int xsz; /*in*/
  brancher *bs; /*in*/
  int bsz; /*in*/
  brancher _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_var_choice(_v_varc, &varc, _ctx);
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(atom ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_atom_atom(_v3, &xs[_c2], _ctx);
  }
  xsz = _c1;
  _c4 = Wosize_val(_v_bs);
  bs = camlidl_malloc(_c4 * sizeof(brancher ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_bs, _c5);
    camlidl_ml2c_solver_brancher(_v6, &bs[_c5], _ctx);
  }
  bsz = _c4;
  _res = new_bool_priority_brancher(varc, xs, xsz, bs, bsz);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_new_int_priority_brancher(
	value _v_varc,
	value _v_xs,
	value _v_bs)
{
  var_choice varc; /*in*/
  intvar *xs; /*in*/
  int xsz; /*in*/
  brancher *bs; /*in*/
  int bsz; /*in*/
  brancher _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  mlsize_t _c4;
  mlsize_t _c5;
  value _v6;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_var_choice(_v_varc, &varc, _ctx);
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(intvar ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_solver_intvar(_v3, &xs[_c2], _ctx);
  }
  xsz = _c1;
  _c4 = Wosize_val(_v_bs);
  bs = camlidl_malloc(_c4 * sizeof(brancher ), _ctx);
  for (_c5 = 0; _c5 < _c4; _c5++) {
    _v6 = Field(_v_bs, _c5);
    camlidl_ml2c_solver_brancher(_v6, &bs[_c5], _ctx);
  }
  bsz = _c4;
  _res = new_int_priority_brancher(varc, xs, xsz, bs, bsz);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_seq_brancher(
	value _v_bs)
{
  brancher *bs; /*in*/
  int sz; /*in*/
  brancher _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _c1 = Wosize_val(_v_bs);
  bs = camlidl_malloc(_c1 * sizeof(brancher ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bs, _c2);
    camlidl_ml2c_solver_brancher(_v3, &bs[_c2], _ctx);
  }
  sz = _c1;
  _res = seq_brancher(bs, sz);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_limit_brancher(
	value _v_base)
{
  brancher base; /*in*/
  brancher _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_brancher(_v_base, &base, _ctx);
  _res = limit_brancher(base);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_warmstart_brancher(
	value _v_xs)
{
  atom *xs; /*in*/
  int sz; /*in*/
  brancher _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _c1 = Wosize_val(_v_xs);
  xs = camlidl_malloc(_c1 * sizeof(atom ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_xs, _c2);
    camlidl_ml2c_atom_atom(_v3, &xs[_c2], _ctx);
  }
  sz = _c1;
  _res = warmstart_brancher(xs, sz);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_toggle_brancher(
	value _v_bs)
{
  brancher *bs; /*in*/
  int sz; /*in*/
  brancher _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _c1 = Wosize_val(_v_bs);
  bs = camlidl_malloc(_c1 * sizeof(brancher ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_bs, _c2);
    camlidl_ml2c_solver_brancher(_v3, &bs[_c2], _ctx);
  }
  sz = _c1;
  _res = toggle_brancher(bs, sz);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_add_brancher(
	value _v_s,
	value _v_b)
{
  solver s; /*in*/
  brancher b; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_solver_brancher(_v_b, &b, _ctx);
  add_brancher(s, b);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_solver_get_brancher(
	value _v_s)
{
  solver s; /*in*/
  brancher _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _res = get_brancher(s);
  _vres = camlidl_c2ml_solver_brancher(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_unlimited(value _unit)
{
  limits _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  _res = unlimited();
  _vres = camlidl_c2ml_solver_limits(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_is_consistent(
	value _v_s)
{
  solver s; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _res = is_consistent(s);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_solve(
	value _v_s,
	value _v_l)
{
  solver s; /*in*/
  limits l; /*in*/
  result _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_solver_limits(_v_l, &l, _ctx);
  _res = solve(s, l);
  _vres = camlidl_c2ml_solver_result(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_abort_solve(
	value _v_s)
{
  solver s; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  abort_solve(s);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_solver_post_atom(
	value _v_s,
	value _v_at)
{
  solver s; /*in*/
  atom at; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_at, &at, _ctx);
  _res = post_atom(s, at);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_post_clause(
	value _v_s,
	value _v_cl)
{
  solver s; /*in*/
  atom *cl; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _c1 = Wosize_val(_v_cl);
  cl = camlidl_malloc(_c1 * sizeof(atom ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_cl, _c2);
    camlidl_ml2c_atom_atom(_v3, &cl[_c2], _ctx);
  }
  sz = _c1;
  _res = post_clause(s, cl, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_assume(
	value _v_s,
	value _v_at)
{
  solver s; /*in*/
  atom at; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_at, &at, _ctx);
  _res = assume(s, at);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_retract(
	value _v_s)
{
  solver s; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  retract(s);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_solver_retract_all(
	value _v_s)
{
  solver s; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  retract_all(s);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_solver_new_intvar(
	value _v_s,
	value _v_lb,
	value _v_ub)
{
  solver s; /*in*/
  int lb; /*in*/
  int ub; /*in*/
  intvar _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  lb = Int_val(_v_lb);
  ub = Int_val(_v_ub);
  _res = new_intvar(s, lb, ub);
  _vres = camlidl_c2ml_solver_intvar(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_permute_intvar(
	value _v_s,
	value _v_x,
	value _v_vals)
{
  solver s; /*in*/
  intvar x; /*in*/
  int *vals; /*in*/
  int sz; /*in*/
  intvar _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _c1 = Wosize_val(_v_vals);
  vals = camlidl_malloc(_c1 * sizeof(int ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_vals, _c2);
    vals[_c2] = Int_val(_v3);
  }
  sz = _c1;
  _res = permute_intvar(s, x, vals, sz);
  _vres = camlidl_c2ml_solver_intvar(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_intvar_neg(
	value _v_x)
{
  intvar x; /*in*/
  intvar _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _res = intvar_neg(x);
  _vres = camlidl_c2ml_solver_intvar(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_intvar_plus(
	value _v_x,
	value _v_k)
{
  intvar x; /*in*/
  int k; /*in*/
  intvar _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  k = Int_val(_v_k);
  _res = intvar_plus(x, k);
  _vres = camlidl_c2ml_solver_intvar(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_make_sparse(
	value _v_x,
	value _v_vals)
{
  intvar x; /*in*/
  int *vals; /*in*/
  int sz; /*in*/
  int _res;
  mlsize_t _c1;
  mlsize_t _c2;
  value _v3;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _c1 = Wosize_val(_v_vals);
  vals = camlidl_malloc(_c1 * sizeof(int ), _ctx);
  for (_c2 = 0; _c2 < _c1; _c2++) {
    _v3 = Field(_v_vals, _c2);
    vals[_c2] = Int_val(_v3);
  }
  sz = _c1;
  _res = make_sparse(x, vals, sz);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_new_boolvar(
	value _v_s)
{
  solver s; /*in*/
  atom _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _res = new_boolvar(s);
  _vres = camlidl_c2ml_atom_atom(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_slice_of_intvar(
	value _v_x)
{
  intvar x; /*in*/
  intslice _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  _res = slice_of_intvar(x);
  _vres = camlidl_c2ml_solver_intslice(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_slice_from(
	value _v_x,
	value _v_lb)
{
  intslice x; /*in*/
  int lb; /*in*/
  intslice _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intslice(_v_x, &x, _ctx);
  lb = Int_val(_v_lb);
  _res = slice_from(x, lb);
  _vres = camlidl_c2ml_solver_intslice(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_slice_upto(
	value _v_x,
	value _v_ub)
{
  intslice x; /*in*/
  int ub; /*in*/
  intslice _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intslice(_v_x, &x, _ctx);
  ub = Int_val(_v_ub);
  _res = slice_upto(x, ub);
  _vres = camlidl_c2ml_solver_intslice(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_slice_rezero(
	value _v_x,
	value _v_zero_val)
{
  intslice x; /*in*/
  int zero_val; /*in*/
  intslice _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intslice(_v_x, &x, _ctx);
  zero_val = Int_val(_v_zero_val);
  _res = slice_rezero(x, zero_val);
  _vres = camlidl_c2ml_solver_intslice(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_new_floatvar(
	value _v_s,
	value _v_lb,
	value _v_ub)
{
  solver s; /*in*/
  float lb; /*in*/
  float ub; /*in*/
  fpvar _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  lb = Double_val(_v_lb);
  ub = Double_val(_v_ub);
  _res = new_floatvar(s, lb, ub);
  _vres = camlidl_c2ml_solver_fpvar(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_set_bool_polarity(
	value _v_s,
	value _v_at,
	value _v_pol)
{
  solver s; /*in*/
  atom at; /*in*/
  int pol; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_atom_atom(_v_at, &at, _ctx);
  pol = Int_val(_v_pol);
  set_bool_polarity(s, at, pol);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_solver_set_int_polarity(
	value _v_x,
	value _v_pol)
{
  intvar x; /*in*/
  int pol; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_x, &x, _ctx);
  pol = Int_val(_v_pol);
  set_int_polarity(x, pol);
  camlidl_free(_ctx);
  return Val_unit;
}

value camlidl_solver_ivar_pid(
	value _v_v)
{
  intvar v; /*in*/
  pred_t _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  _res = ivar_pid(v);
  _vres = camlidl_c2ml_atom_pred_t(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_ivar_lb(
	value _v_v)
{
  intvar v; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  _res = ivar_lb(v);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_ivar_ub(
	value _v_v)
{
  intvar v; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  _res = ivar_ub(v);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_current_ivar_lb(
	value _v_v)
{
  intvar v; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  _res = current_ivar_lb(v);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_current_ivar_ub(
	value _v_v)
{
  intvar v; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  _res = current_ivar_ub(v);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_suggest_ivar_value(
	value _v_s,
	value _v_v)
{
  solver s; /*in*/
  intvar v; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  _res = suggest_ivar_value(s, v);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_get_model(
	value _v_s)
{
  solver s; /*in*/
  model _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _res = get_model(s);
  _vres = camlidl_c2ml_solver_model(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_int_value(
	value _v_m,
	value _v_v)
{
  model m; /*in*/
  intvar v; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_model(_v_m, &m, _ctx);
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  _res = int_value(m, v);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_intslice_value(
	value _v_m,
	value _v_v)
{
  model m; /*in*/
  intslice v; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_model(_v_m, &m, _ctx);
  camlidl_ml2c_solver_intslice(_v_v, &v, _ctx);
  _res = intslice_value(m, v);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_float_value(
	value _v_m,
	value _v_v)
{
  model m; /*in*/
  fpvar v; /*in*/
  float _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_model(_v_m, &m, _ctx);
  camlidl_ml2c_solver_fpvar(_v_v, &v, _ctx);
  _res = float_value(m, v);
  _vres = caml_copy_double(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_atom_value(
	value _v_m,
	value _v_at)
{
  model m; /*in*/
  atom at; /*in*/
  int _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_model(_v_m, &m, _ctx);
  camlidl_ml2c_atom_atom(_v_at, &at, _ctx);
  _res = atom_value(m, at);
  _vres = Val_int(_res);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_ivar_le(
	value _v_v,
	value _v_k)
{
  intvar v; /*in*/
  int k; /*in*/
  atom _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  k = Int_val(_v_k);
  _res = ivar_le(v, k);
  _vres = camlidl_c2ml_atom_atom(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_ivar_eq(
	value _v_v,
	value _v_k)
{
  intvar v; /*in*/
  int k; /*in*/
  atom _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intvar(_v_v, &v, _ctx);
  k = Int_val(_v_k);
  _res = ivar_eq(v, k);
  _vres = camlidl_c2ml_atom_atom(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_islice_le(
	value _v_v,
	value _v_k)
{
  intslice v; /*in*/
  int k; /*in*/
  atom _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_intslice(_v_v, &v, _ctx);
  k = Int_val(_v_k);
  _res = islice_le(v, k);
  _vres = camlidl_c2ml_atom_atom(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_fpvar_le(
	value _v_v,
	value _v_k)
{
  fpvar v; /*in*/
  float k; /*in*/
  atom _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_fpvar(_v_v, &v, _ctx);
  k = Double_val(_v_k);
  _res = fpvar_le(v, k);
  _vres = camlidl_c2ml_atom_atom(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_fpvar_lt(
	value _v_v,
	value _v_k)
{
  fpvar v; /*in*/
  float k; /*in*/
  atom _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_fpvar(_v_v, &v, _ctx);
  k = Double_val(_v_k);
  _res = fpvar_lt(v, k);
  _vres = camlidl_c2ml_atom_atom(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_new_pred(
	value _v_s,
	value _v_lb,
	value _v_ub)
{
  solver s; /*in*/
  int lb; /*in*/
  int ub; /*in*/
  pred_t _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  lb = Int_val(_v_lb);
  ub = Int_val(_v_ub);
  _res = new_pred(s, lb, ub);
  _vres = camlidl_c2ml_atom_pred_t(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_pred_ge(
	value _v_p,
	value _v_k)
{
  pred_t p; /*in*/
  int k; /*in*/
  atom _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_atom_pred_t(_v_p, &p, _ctx);
  k = Int_val(_v_k);
  _res = pred_ge(p, k);
  _vres = camlidl_c2ml_atom_atom(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_get_statistics(
	value _v_s)
{
  solver s; /*in*/
  statistics _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  _res = get_statistics(s);
  _vres = camlidl_c2ml_solver_statistics(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_solver_set_cons_id(
	value _v_s,
	value _v_id)
{
  solver s; /*in*/
  int id; /*in*/
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_solver_solver(_v_s, &s, _ctx);
  id = Int_val(_v_id);
  set_cons_id(s, id);
  camlidl_free(_ctx);
  return Val_unit;
}

