#include <geas/solver/solver.h>
#include <geas/solver/model.h>
#include <geas/solver/branch.h>
#include <geas/solver/priority-branch.h>
#include <geas/engine/logging.h>

#include <geas/utils/defs.h>

#include <geas/c/geas.h>
#include <geas/c/marshal.h>

#ifdef __cplusplus
extern "C" {
#endif

const atom at_True = unget_atom(geas::at_True);

atom neg(atom at) {
  return unget_atom(~get_atom(at));
}

pval_t pval_inv(pval_t p) { return geas::pval_inv(p); }
int64_t to_int(pval_t p) { return geas::to_int(p); }
//atom at_true(void) {
//    
//}

options default_opts(void) { return default_options; }
solver new_solver(options o) {
  return (solver) (new geas::solver(o));
}

void destroy_solver(solver s) {
  delete get_solver(s);
}

intvar new_intvar(solver s, int lb, int ub) {
  geas::solver* ps(get_solver(s));
  geas::intvar* v(new geas::intvar(ps->new_intvar(lb, ub)));
  return (intvar) v;
}

intvar permute_intvar(solver s, intvar x, int* ks, int sz) {
  vec<int> vals(ks, ks+sz);
  geas::intvar* v(new geas::intvar(geas::permute_intvar(get_solver(s)->data, *get_intvar(x), vals)));
  return (intvar) v;
}
/*
typedef geas::optvar<geas::intvar> o_intvar;
intvar new_opt_intvar(solver s, int lb, int ub) {
  geas::solver* ps(get_solver(s));
  o_intvar* v(new o_intvar(ps->new_opt_intvar(lb, ub)));
  return (o_intvar) v;
}
*/

intvar intvar_neg(intvar x) {
  geas::intvar* v(new geas::intvar(-(*((geas::intvar*) x))));
  return (intvar) v;
}

intvar intvar_plus(intvar x, int k) {
  geas::intvar* v(new geas::intvar(*((geas::intvar*) x) + k));
  return (intvar) v;
}

int make_sparse(intvar px, int* vals, int sz) {
  geas::intvar* x((geas::intvar*) px);
  vec<geas::intvar::val_t> vs;
  for(int* v = vals; v < vals+sz; ++v)
    vs.push(*v);
  return geas::make_sparse(*x, vs);
}

void destroy_intvar(intvar v) {
  delete get_intvar(v);
}

int compare_intvar(intvar x, intvar y) {
  if(get_intvar(x)->p == get_intvar(y)->p)
    return get_intvar(x)->off - get_intvar(y)->off;
  return get_intvar(x)->p - get_intvar(y)->p;
}

intslice slice_of_intvar(intvar x) {
  geas::int_slice s(geas::int_slice::from_intvar(*get_intvar(x)));
  return (intslice) (new geas::int_slice(s));
}
intslice slice_from(intslice s, int lb) {
  geas::int_slice gs(*get_intslice(s));
  return (intslice) (new geas::int_slice(gs.from(lb)));
}
intslice slice_upto(intslice s, int ub) {
  geas::int_slice gs(*get_intslice(s));
  return (intslice) (new geas::int_slice(gs.upto(ub)));
}
intslice slice_rezero(intslice s, int zero_val) {
  geas::int_slice gs(*get_intslice(s));
  return (intslice) (new geas::int_slice(gs.re_zero(zero_val)));
}

void destroy_intslice(intslice s) {
  delete get_intslice(s);
}
int compare_intslice(intslice s, intslice t) {
  geas::int_slice gs(*get_intslice(s));
  geas::int_slice gt(*get_intslice(t));
  if(gs.p != gt.p)
    return gs.p - gt.p;
  if(gs.lb_pos != gt.lb_pos)
    return gs.lb_val - gt.lb_val;
  if(gs.lb_val != gt.lb_val)
    return gs.lb_val - gt.lb_val;
  return gs.delta - gt.delta;
}
long hash_intslice(intslice s) {
  geas::int_slice gs(*get_intslice(s));
  unsigned long hash = 5381;
  hash = ((hash<<5) + hash) + gs.p;
  hash = ((hash<<5) + hash) + gs.lb_pos;
  hash = ((hash<<5) + hash) + gs.lb_val;
  hash = ((hash<<5) + hash) + gs.delta;
  return hash;
}


int solver_id(solver s) {
  return reinterpret_cast<uintptr_t>(get_solver(s));
}

long hash_intvar(intvar x) {
  unsigned long hash = 5381;
  hash = ((hash<<5) + hash) + get_intvar(x)->p;
  hash = ((hash<<5) + hash) + get_intvar(x)->off;
  return hash;
}

fpvar new_floatvar(solver s, float lb, float ub) {
  geas::solver* ps(get_solver(s));
  geas::fp::fpvar* v(new geas::fp::fpvar(ps->new_floatvar(lb, ub)));
  return (fpvar) v;
}

void destroy_floatvar(fpvar v) {
  delete get_fpvar(v);
}

static forceinline geas::VarChoice get_varc(var_choice c) {
  switch(c) {
    case VAR_INORDER: return geas::Var_InputOrder;
    case VAR_FIRSTFAIL: return geas::Var_FirstFail;
    case VAR_LEAST: return geas::Var_Smallest;
    case VAR_GREATEST: return geas::Var_Largest;
  }
  GEAS_ERROR;
  return geas::Var_Smallest;
}

static forceinline geas::ValChoice get_valc(val_choice c) {
  switch(c) {
    case VAL_MIN: return geas::Val_Min;
    case VAL_MAX: return geas::Val_Max;
    case VAL_SPLIT: return geas::Val_Split;
  }
  GEAS_ERROR;
  return geas::Val_Min;
}

brancher new_int_brancher(var_choice varc, val_choice valc, intvar* vs, int sz) {
#if 1
  vec<geas::pid_t> vars;
  intvar* end = vs+sz;
  for(; vs != end; ++vs)
    vars.push(get_intvar(*vs)->p);
  return ((brancher) geas::basic_brancher(get_varc(varc), get_valc(valc), vars));
#else
  vec<geas::intvar> vars;
  intvar* end = vs+sz;
  for(; vs != end; ++vs)
    vars.push(*get_intvar(*vs));
  geas::var_chooser<geas::intvar> score(get_varc(varc));  
  geas::val_chooser<geas::intvar> sel(get_valc(valc));
  return ((brancher) new geas::score_brancher<geas::intvar, geas::var_chooser<geas::intvar>, geas::val_chooser<geas::intvar>>(score, sel, vars));
#endif
}

brancher new_bool_brancher(var_choice varc, val_choice valc, atom* vs, int sz) {
  vec<geas::pid_t> vars;
  atom* end = vs+sz;
  for(; vs != end; ++vs)
    vars.push(get_atom(*vs).pid);
  return ((brancher) geas::basic_brancher(get_varc(varc), get_valc(valc), vars));
}

brancher new_bool_priority_brancher(var_choice varc,
  atom* vs, int vsz, brancher* bs, int bsz) {
  int sz = std::min(vsz, bsz);
  atom* end = vs + sz;
  vec<geas::patom_t> sel;
  vec<geas::brancher*> br;

  for(; vs != end; ++vs, ++bs) {
    sel.push(get_atom(*vs));
    br.push((geas::brancher*) (*bs));
  }
  return ((brancher) geas::priority_brancher(get_varc(varc), sel, br));
}

brancher new_int_priority_brancher(var_choice varc,
  intvar* vs, int vsz, brancher* bs, int bsz) {
  int sz = std::min(vsz, bsz);
  intvar* end = vs + sz;
  vec<geas::intvar> sel;
  vec<geas::brancher*> br;

  for(; vs != end; ++vs, ++bs) {
    sel.push(*get_intvar(*vs));
    br.push((geas::brancher*) (*bs));
  }
  return ((brancher) geas::priority_brancher(get_varc(varc), sel, br));
}

brancher seq_brancher(brancher* bs, int sz) {
  vec<geas::brancher*> branchers;
  brancher* end = bs + sz;
  for(; bs != end; ++bs)
    branchers.push((geas::brancher*) (*bs));
  return ((brancher) geas::seq_brancher(branchers));
}


brancher limit_brancher(brancher b) {
  return (brancher) geas::limit_brancher((geas::brancher*) b);
}
brancher warmstart_brancher(atom* xs, int sz) {
  vec<geas::patom_t> decs; 
  for(atom at : range(xs, xs+sz)) {
    decs.push(get_atom(at));
  }

  return (brancher) geas::warmstart_brancher(decs);
}

brancher toggle_brancher(brancher* ts, int sz) {
  vec<geas::brancher*> bs;
  brancher* end = ts + sz;
  for(; ts != end; ++ts)
    bs.push((geas::brancher*) (*ts));
  return (brancher) geas::toggle_brancher(bs);
}

void add_brancher(solver s, brancher b) {
  get_solver(s)->data->branchers.push((geas::brancher*) b);
}
brancher get_brancher(solver s) {
  return (brancher) get_solver(s)->data->last_branch;
}

limits unlimited(void) { return limits { 0, 0 }; }
limits time_limit(int s) { return limits { (double) s, 0 }; }
limits conflict_limit(int c) { return limits { 0, c }; }

int is_consistent(solver s) {
  return get_solver(s)->is_consistent();
}

result solve(solver s, limits lim) {
  // Currently ignoring conflict limit
  return unget_result(get_solver(s)->solve(lim)); 
}

void abort_solve(solver s) { return get_solver(s)->abort(); }

void reset(solver s) {
  geas::solver_data* sd = get_solver(s)->data;
  if(sd->infer.trail_lim.size() > 0)
    geas::bt_to_level(sd, 0);
}

int post_atom(solver s, atom at) {
  reset(s);
  return get_solver(s)->post(get_atom(at));
}

int assume(solver s, atom at) {
  return get_solver(s)->assume(get_atom(at));
}
void retract(solver s) {
  get_solver(s)->retract();
}
void retract_all(solver s) {
  get_solver(s)->clear_assumptions();
}

void get_conflict(solver s, atom** at, int* out_sz) {
  vec<geas::patom_t> confl;
  get_solver(s)->get_conflict(confl);

  *out_sz = confl.size();
  *at = (atom*) malloc(sizeof(atom) * confl.size());
  for(int ii = 0; ii < confl.size(); ++ii) {
    (*at)[ii] = unget_atom(confl[ii]);
  }
}

void get_assumption_inferences(solver s, atom** at, int* out_sz) {
  vec<geas::patom_t> infs;
/*
  get_solver(s)->assumption_inferences(infs);
*/
  *out_sz = infs.size();
  *at = (atom*) malloc(sizeof(atom) * infs.size());
  for(int ii = 0; ii < infs.size(); ++ii)
    (*at)[ii] = unget_atom(infs[ii]);
}

// acts is allocated, must be freed by caller.
void get_ivar_activities(solver s, intvar* xs, int sz, double** acts) {
  double* dest = (double*) malloc(sizeof(double) * sz);
  *acts = dest;

  geas::solver_data* d(get_solver(s)->data);

  intvar* end = xs+sz;
  for(; xs != end; ++xs, ++dest) {
    *dest = d->infer.pred_act[get_intvar(*xs)->p>>1];
  }
}

int suggest_ivar_value(solver _s, intvar _x) {
  geas::solver_data* d(get_solver(_s)->data);
  geas::intvar* x(get_intvar(_x));
  pval_t p(d->confl.pred_saved[x->p>>1].val);

  return (x->p&1) ? x->ub_of_pval(p) : x->lb_of_pval(p);
}

int post_clause(solver s, atom* cl, int sz) {
  reset(s);
  vec<geas::clause_elt> elts;
  for(int ii : irange(sz))
    elts.push(get_atom(cl[ii]));
  return add_clause(*get_solver(s)->data, elts);
}

atom new_boolvar(solver s) {
  return unget_atom(get_solver(s)->new_boolvar());
}

void set_bool_polarity(solver s, atom at, int pol) {
  geas::solver_data* d = get_solver(s)->data;
  pid_t p = get_atom(at).pid;

  d->polarity[p>>1].preferred = d->polarity[p>>1].branch = pol^(p&1);
  d->confl.pred_saved[p>>1].val = geas::from_int(p&1);
}

void set_int_polarity(intvar x, int pol) {
  geas::solver_data* d = get_intvar(x)->ext->s;
  pid_t p = get_intvar(x)->p;

  d->polarity[p>>1].preferred = d->polarity[p>>1].branch = pol^(p&1);
  if(p&1)
    d->confl.pred_saved[p>>1].val = geas::pval_inv(d->state.p_root[p]);
  else
    d->confl.pred_saved[p>>1].val = d->state.p_root[p];
}

model get_model(solver s) {
  geas::model* m(new geas::model(get_solver(s)->get_model()));
  return (model) m;
}

void destroy_model(model m) {
  delete get_model(m);
}

int int_value(model m, intvar v) {
  return get_intvar(v)->model_val(*get_model(m));
}
int intslice_value(model m, intslice v) {
  return get_intslice(v)->model_val(*get_model(m));
}
float float_value(model m, fpvar v) {
  return get_fpvar(v)->model_val(*get_model(m));
}

pred_id_t ivar_pid(intvar v) { return get_intvar(v)->p; }

int ivar_lb(intvar v) {
  geas::solver_data* s = get_intvar(v)->ext->s;
  return get_intvar(v)->lb(s->state.p_root);
}
int ivar_ub(intvar v) {
  geas::solver_data* s = get_intvar(v)->ext->s;
  return get_intvar(v)->ub(s->state.p_root);
}
int current_ivar_lb(intvar v) {
  geas::solver_data* s = get_intvar(v)->ext->s;
  return get_intvar(v)->lb(s->state.p_vals);
}
int current_ivar_ub(intvar v) {
  geas::solver_data* s = get_intvar(v)->ext->s;
  return get_intvar(v)->ub(s->state.p_vals);
}

int atom_value(model m, atom at) {
  return get_model(m)->value(get_atom(at));
}

atom ivar_le(intvar v, int k) {
  return unget_atom( (*get_intvar(v)) <= k );
}

atom ivar_eq(intvar v, int k) {
  return unget_atom( (*get_intvar(v)) == k );
}

atom islice_le(intslice v, int k) {
  return unget_atom( (*get_intslice(v)) <= k );
}

atom fpvar_le(fpvar v, float k) {
  return unget_atom( (*get_fpvar(v)) <= k );
}
atom fpvar_lt(fpvar v, float k) {
  return unget_atom( (*get_fpvar(v)) < k );
}

pred_t new_pred(solver s, int lb, int ub) {
  return geas::new_pred(*(get_solver(s)->data),
    geas::from_int(lb), geas::from_int(ub));
}

atom pred_ge(pred_t p, int k) {
  return unget_atom(geas::patom_t(p, k));
}

statistics get_statistics(solver s) {
  geas::solver_data* data(get_solver(s)->data);

  /*
  statistics st = {
    data->stats.solutions,
    data->stats.conflicts,
    data->stats.restarts
  };
  */
  return data->stats;
}

void set_cons_id(solver s, int id) {
  get_solver(s)->data->log.scope_constraint = id;
}

void set_log_file(solver s, FILE* f) {
  get_solver(s)->data->log.log_file = f;
}

#ifdef __cplusplus
}
#endif
