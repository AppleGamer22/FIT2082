/* File generated from atom.idl */

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

#include <geas/c/atom.h>
void camlidl_ml2c_atom_pred_t(value _v1, pred_t * _c2, camlidl_ctx _ctx)
{
  (*_c2) = Int32_val(_v1);
}

value camlidl_c2ml_atom_pred_t(pred_t * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = caml_copy_int32((*_c2));
  return _v1;
}

void camlidl_ml2c_atom_pval_t(value _v1, pval_t * _c2, camlidl_ctx _ctx)
{
  (*_c2) = Int64_val(_v1);
}

value camlidl_c2ml_atom_pval_t(pval_t * _c2, camlidl_ctx _ctx)
{
value _v1;
  _v1 = caml_copy_int64((*_c2));
  return _v1;
}

void camlidl_ml2c_atom_atom(value _v1, atom * _c2, camlidl_ctx _ctx)
{
value _v3;
value _v4;
  _v3 = Field(_v1, 0);
  (*_c2).pid = Int32_val(_v3);
  _v4 = Field(_v1, 1);
  (*_c2).val = Int64_val(_v4);
}

value camlidl_c2ml_atom_atom(atom * _c2, camlidl_ctx _ctx)
{
value _v1;
value _v3[2];
  _v3[0] = _v3[1] = 0;
  Begin_roots_block(_v3, 2)
    _v3[0] = caml_copy_int32((*_c2).pid);
    _v3[1] = caml_copy_int64((*_c2).val);
    _v1 = camlidl_alloc_small(2, 0);
    Field(_v1, 0) = _v3[0];
    Field(_v1, 1) = _v3[1];
  End_roots()
  return _v1;
}

value camlidl_atom_neg(
	value _v_at)
{
  atom at; /*in*/
  atom _res;
  value _vres;

  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;
  camlidl_ml2c_atom_atom(_v_at, &at, _ctx);
  _res = neg(at);
  _vres = camlidl_c2ml_atom_atom(&_res, _ctx);
  camlidl_free(_ctx);
  return _vres;
}

value camlidl_atom_to_int(
	value _v_val)
{
  unsigned long val; /*in*/
  long _res;
  value _vres;

  val = Int64_val(_v_val);
  _res = to_int(val);
  _vres = caml_copy_int64(_res);
  return _vres;
}

value camlidl_atom_pval_inv(
	value _v_val)
{
  unsigned long val; /*in*/
  unsigned long _res;
  value _vres;

  val = Int64_val(_v_val);
  _res = pval_inv(val);
  _vres = caml_copy_int64(_res);
  return _vres;
}

