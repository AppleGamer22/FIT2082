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

extern value camlidl_c2ml_atom_atom(atom *, camlidl_ctx _ctx);

CAMLprim value ml_get_conflict(value _s) {
  CAMLparam1 (_s);
  CAMLlocal2 (_at, _res);
  
  atom* arr;
  int sz;
  int ii; 
  
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;

  get_conflict(*((solver*) Data_custom_val(_s)), &arr, &sz);
  
  _res = caml_alloc(sz, 0);
  for(ii = 0; ii < sz; ii++) {
    _at = camlidl_c2ml_atom_atom(arr+ii, _ctx);
    Store_field(_res, ii, _at);
  }
  camlidl_free(_ctx);
  free(arr);
  CAMLreturn (_res);
}

CAMLprim value ml_assumption_inferences(value _s) {
  CAMLparam1 (_s);
  CAMLlocal2 (_at, _res);
  
  atom* arr;
  int sz;
  int ii; 
  
  struct camlidl_ctx_struct _ctxs = { CAMLIDL_TRANSIENT, NULL };
  camlidl_ctx _ctx = &_ctxs;

  get_assumption_inferences(*((solver*) Data_custom_val(_s)), &arr, &sz);
  
  _res = caml_alloc(sz, 0);
  for(ii = 0; ii < sz; ii++) {
    _at = camlidl_c2ml_atom_atom(arr+ii, _ctx);
    Store_field(_res, ii, _at);
  }
  camlidl_free(_ctx);
  free(arr);
  CAMLreturn (_res);
}

CAMLprim value ml_get_ivar_activities(value _s, value _xs) {
  CAMLparam2 (_s, _xs);
  CAMLlocal1 (_acts);
  
  // This is kind of double-handling. Would be more efficient to
  // bypass the C interface...
  int sz = Wosize_val(_xs);

  intvar* xs = (intvar*) malloc(sizeof(intvar) * sz);
  for(int ii = 0; ii < sz; ++ii) {
    xs[ii] = *((intvar*) Data_custom_val(Field(_xs, ii)));
  }
  double* c_acts = NULL; // Allocated by callee
  get_ivar_activities(*((solver*) Data_custom_val(_s)), xs, sz, &c_acts);

  _acts = caml_alloc(sz, Double_array_tag);
  for(int ii = 0; ii < sz; ii++) {
    Store_double_field(_acts, ii, c_acts[ii]);
  }
  free(xs);
  free(c_acts);

  CAMLreturn (_acts);
}
