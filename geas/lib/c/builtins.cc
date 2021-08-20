#include <geas/mtl/Vec.h>
#include <geas/utils/defs.h>

#include <geas/c/atom.h>
#include <geas/c/geas.h>
#include <geas/c/builtins.h>

#include <geas/c/marshal.h>

#include <geas/solver/solver_data.h>
#include <geas/constraints/builtins.h>
#include <geas/constraints/flow/flow.h>
#include <geas/constraints/linear-par.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
int clause(solver s, atom* cl, int sz) {
  vec<geas::clause_elt> elts;
  for(int ii : irange(sz))
    elts.push(get_atom(cl[ii]));
  return add_clause(*get_solver(s)->data, elts);
}
*/

// These are half-reified.
// For strict versions, call with r = at_True
int linear_le(solver s, atom r, int_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<geas::intvar> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(*get_intvar(ts[ii].x));
  }
#if 0
  if(xs.size() > 5)
    return geas::linear_le_ps(get_solver(s)->data, ks, xs,  k, get_atom(r));
  else
    return geas::linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
#else
  return geas::linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
#endif

}

int slice_linear_le(solver s, atom r, slice_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<geas::int_slice> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(*get_intslice(ts[ii].x));
  }
  // return geas::linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
  return geas::lin_leq<int, geas::int_slice>::post(get_solver(s)->data, ks, xs, k, get_atom(r));
  return true;
}

int linear_ne(solver s, atom r, int_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<geas::intvar> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(*get_intvar(ts[ii].x));
  }
  return geas::linear_ne(get_solver(s)->data, ks, xs,  k, get_atom(r));
}

/*
int bool_linear_le(solver s, atom r, at_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<geas::patom_t> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(get_atom(ts[ii].x));
  }
  return geas::bool_linear_le(get_solver(s)->data, ks, xs,  k, get_atom(r));
}
*/
int bool_linear_le(solver s, atom r, intvar z, at_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<geas::patom_t> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(get_atom(ts[ii].x));
  }
  return geas::bool_linear_le(get_solver(s)->data, get_atom(r), *get_intvar(z), ks, xs,  k);
}
int bool_linear_ge(solver s, atom r, intvar z,  at_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<geas::patom_t> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(get_atom(ts[ii].x));
  }
  return geas::bool_linear_ge(get_solver(s)->data, get_atom(r), *get_intvar(z), ks, xs,  k);
}

int atmost_1(solver s, atom r, atom* xs, int sz) {
  vec<geas::patom_t> ys;
  for(int ii : irange(sz))
    ys.push(get_atom(xs[ii]));
  return geas::atmost_1(get_solver(s)->data, ys, get_atom(r));
}

int atmost_k(solver s, atom r, atom* xs, int sz, int k) {
  vec<geas::patom_t> ys;
  for(int ii : irange(sz))
    ys.push(get_atom(xs[ii]));
  return geas::atmost_k(get_solver(s)->data, ys, k, get_atom(r));
}

int bool_linear_ne(solver s, atom r, at_linterm* ts, int sz, int k) {
  vec<int> ks;
  vec<geas::patom_t> xs;
  for(int ii = 0; ii < sz; ii++) {
    ks.push(ts[ii].c);
    xs.push(get_atom(ts[ii].x));
  }
  return geas::bool_linear_ne(get_solver(s)->data, ks, xs,  k, get_atom(r));
}


int int_mul(solver s, atom r, intvar z, intvar x, intvar y) {
  return geas::int_mul(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), *get_intvar(y),
                        get_atom(r));
}
int int_div(solver s, atom r, intvar z, intvar x, intvar y) {
  return geas::int_div(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), *get_intvar(y),
                        get_atom(r));
}

int int_abs(solver s, atom r, intvar z, intvar x) {
  return geas::int_abs(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), get_atom(r));
}

int int_max(solver s, atom r, intvar z, intvar* xs, int sz) {
  vec<geas::intvar> p_xs;
  for(intvar* v = xs; v != xs+sz; ++v) {
    p_xs.push(*get_intvar(*v));
  }
  return geas::int_max(get_solver(s)->data,
                        *get_intvar(z), p_xs, get_atom(r));
}

int int_element(solver s, atom r, intvar z, intvar x, int* elts, int sz) {
  vec<int> p_elts;
  for(int* v = elts; v != elts+sz; ++v) {
    p_elts.push(*v);
  }
  return geas::int_element(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), p_elts, get_atom(r));
}


int var_int_element(solver s, atom r, intvar z, intvar x, intvar* elts, int sz) {
  vec<geas::intvar> p_elts;
  for(intvar* v = elts; v != elts+sz; ++v) {
    p_elts.push(*get_intvar(*v));
  }
  return geas::var_int_element(get_solver(s)->data,
                        *get_intvar(z), *get_intvar(x), p_elts, get_atom(r));
}

int int_le(solver s, atom r, intvar x, intvar y, int k) {
  return geas::int_le(get_solver(s)->data,
                    *get_intvar(x), *get_intvar(y), k, get_atom(r));
}

int int_ne(solver s, atom r, intvar x, intvar y) {
  return geas::int_ne(get_solver(s)->data,
                    *get_intvar(x), *get_intvar(y), get_atom(r));
}
int int_eq(solver s, atom r, intvar x, intvar y) {
  return geas::int_eq(get_solver(s)->data,
                    *get_intvar(x), *get_intvar(y), get_atom(r));
}

int all_different_int(solver s, intvar* xs, int sz) {
  if(sz == 0)
    return true;

  vec<geas::intvar> p_xs;
  for(intvar* v = xs; v != xs+sz; ++v) {
    p_xs.push(*get_intvar(*v));
  }
#if 1
  return geas::all_different_int(get_solver(s)->data, p_xs);
#else
  /*
  vec<int> ds(p_xs.size(), 1);
  return geas::disjunctive_int(get_solver(s)->data, p_xs, ds);
  */
  // Find the min and max-domains.
  geas::solver_data* sd(get_solver(s)->data);
  int lb = p_xs[0].lb(sd); 
  int ub = p_xs[0].ub(sd); 
  for(int ii = 1; ii < p_xs.size(); ii++) {
    lb = std::min(lb, (int) p_xs[ii].lb(sd));
    ub = std::max(ub, (int) p_xs[ii].ub(sd));
  }

  int dom = ub - lb + 1;
  if(p_xs.size() == dom) {
    vec<int> srcs(p_xs.size(), 1);
    vec<int> sinks(p_xs.size(), 1);

    vec<geas::bflow> flows;
    for(int xi : irange(p_xs.size())) {
      for(int k : irange(dom)) {
        flows.push(geas::bflow {xi, k, p_xs[xi] == lb+k }); 
      }
    }
    return geas::bipartite_flow(sd, srcs, sinks, flows);
  } else {
    return geas::all_different_int(sd, p_xs);
  }
#endif
}

int all_different_except_0(solver s, intvar* xs, int sz) {
  if(sz == 0)
    return true;

  vec<geas::intvar> p_xs;
  for(intvar* v = xs; v != xs+sz; ++v) {
    p_xs.push(*get_intvar(*v));
  }
  return geas::all_different_except_0(get_solver(s)->data, p_xs);
}

int bipartite_flow(solver s, int* srcs, int srcs_sz, int* sinks, int sinks_sz, bp_flow* flows, int flows_sz) {
  vec<int> src_vec;
  for(; srcs_sz; --srcs_sz, ++srcs)
    src_vec.push(*srcs);

  vec<int> sink_vec; 
  for(; sinks_sz; --sinks_sz, ++sinks)
    sink_vec.push(*sinks);

  vec<geas::bflow> flow_vec;
  for(; flows_sz; --flows_sz, ++flows) {
    flow_vec.push(geas::bflow { (*flows).src, (*flows).sink, get_atom((*flows).at) });
  }
  return geas::bipartite_flow(get_solver(s)->data, src_vec, sink_vec, flow_vec);
}

int cumulative(solver s, task* ts, int sz, int cap) {
  vec<geas::intvar> xs;
  vec<int> ds;
  vec<int> rs;
  for(task t : range(ts, ts+sz)) {
    xs.push(*get_intvar(t.start));
    ds.push(t.dur);
    rs.push(t.res);
  }
  return geas::cumulative(get_solver(s)->data, xs, ds, rs, cap);
}

int cumulative_var(solver s, vtask* ts, int sz, intvar cap) {
  vec<geas::intvar> xs;
  vec<geas::intvar> ds;
  vec<geas::intvar> rs;
  for(vtask t : range(ts, ts+sz)) {
    xs.push(*get_intvar(t.start));
    ds.push(*get_intvar(t.dur));
    rs.push(*get_intvar(t.res));
  }
  return geas::cumulative_var(get_solver(s)->data, xs, ds, rs, *get_intvar(cap));
}

int cumulative_float(solver s, ftask* ts, int sz, float cap) {
  vec<geas::intvar> xs;
  vec<int> ds;
  vec<float> rs;
  for(ftask t : range(ts, ts+sz)) {
    xs.push(*get_intvar(t.start));
    ds.push(t.dur);
    rs.push(t.res);
  }
  return geas::cumulative_float(get_solver(s)->data, xs, ds, rs, cap);
}

int disjunctive(solver s, dtask* ts, int sz) {
  vec<geas::intvar> xs;
  vec<int> ds;
  for(dtask t : range(ts, ts+sz)) {
    xs.push(*get_intvar(t.start));
    ds.push(t.dur);
  }
  return geas::disjunctive_int(get_solver(s)->data, xs, ds);
}

int precede_chain_int(solver s, intvar* vs, int sz) {
  vec<geas::intvar> xs;
  intvar* end = vs+sz;
  for(; vs != end; ++vs) {
    xs.push(*get_intvar(*vs));
  }
  return int_precede_chain(get_solver(s)->data, xs);
}

int precede_int(solver s, int pre, int post, intvar* vs, int vs_sz) {
  vec<geas::intvar> xs;
  intvar* end = vs+vs_sz;
  for(; vs != end; ++vs) {
    xs.push(*get_intvar(*vs));
  }
  return geas::int_value_precede(get_solver(s)->data, pre, post, xs);
}

int values_precede_chain_int(solver s, int* ks, int ks_sz,
  intvar* vs, int vs_sz) {
  vec<int> vals(ks, ks+ks_sz);
  vec<geas::intvar> xs;
  intvar* end = vs+vs_sz;
  for(; vs != end; ++vs) {
    xs.push(*get_intvar(*vs));
  }
  //return geas::int_precede_chain::post(get_solver(s)->data, xs);
  GEAS_NOT_YET;
  return false;
}

table_id build_table(solver s, int arity, int* elts, int sz) {
  // Build the rows.
  assert(sz % arity == 0);
  int* end(elts+sz);

  vec< vec<int> > rows;
  while(elts != end) {
    rows.push();
    vec<int>& r(rows.last());

    for(int ii = 0; ii < arity; ++ii, ++elts) {
      r.push(*elts);
    }
  }
  return geas::table::build(get_solver(s)->data, rows);
}

int table(solver s, table_id t, intvar* vs, int sz, table_mode m) {
  vec<geas::intvar> xs;
  intvar* end = vs+sz;
  for(; vs != end; ++vs) xs.push(*get_intvar(*vs));

  return geas::table::post(get_solver(s)->data, t, xs, (geas::table::TableMode) m);
}

#ifdef __cplusplus
}
#endif
