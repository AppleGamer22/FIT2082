#include <algorithm>
#include <climits>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/solver/solver_data.h>
#include <geas/vars/intvar.h>
#include <geas/mtl/bool-set.h>
#include <geas/mtl/p-sparse-set.h>
#include <geas/mtl/support-list.h>
#include <geas/utils/interval.h>

#include <geas/constraints/difflogic.h>
#define USE_DIFFLOGIC

// using max = std::max;
// using min = std::min;

namespace geas {

// Deciding whether to decompose
bool is_small(solver_data* s, intvar x) {
  return x.ub(s) - x.lb(s) < s->opts.eager_threshold;
}

class iprod_nonneg : public propagator, public prop_inst<iprod_nonneg> {
  // Queueing
  enum Status { S_Red = 2 };

  watch_result wake(int _xi) {
    if(status & S_Red)
      return Wt_Keep;

    queue_prop();
    return Wt_Keep;
  }

  // Explanations
  void ex_z_lb(int _xi, pval_t pval, vec<clause_elt>& expl) {
    int z_lb = z.lb_of_pval(pval);
    // Need to pick k <= lb(x), k' <= lb(y) s.t. k * k' >= z_lb.
//    int x_lb = lb(xs[0]); int y_lb = lb(xs[1]);

    // Check if we can get by with just one atom.
    for(int xi : irange(2)) {
      int x_lb0 = lb_0(xs[xi]);
      int y_lb = lb(xs[1 - xi]);
      if(x_lb0 * y_lb >= z_lb) {
        expl.push(xs[1 - xi] < iceil(z_lb, x_lb0));
        return;
      }
    }

    int ex = iceil(z_lb, lb(xs[1]));
    int ey = iceil(z_lb, ex);
    expl.push(xs[0] < ex);
    expl.push(xs[1] < ey);
  }

  void ex_z_ub(int _xi, pval_t pval, vec<clause_elt>& expl) {
    int z_ub = z.ub_of_pval(pval);
//    int x_ub = ub(xs[0]); int y_ub = ub(xs[1]);

    for(int xi : irange(2)) {
      int x_ub0 = ub_0(xs[xi]);
      int y_ub = ub(xs[1 - xi]);
      if(x_ub0 * y_ub <= z_ub) {
        assert(x_ub0 * (1 + (z_ub / x_ub0)) > z_ub);
        EX_PUSH(expl, xs[1 - xi] > z_ub/x_ub0);
        return;
      }
    }
    // We need ex * ey <= z_ub.
    int y_ub = ub(xs[1]);
    // int ex = iceil(z_ub,y_ub);
    // int ey = iceil(z_ub,ex);
    int ex = z_ub/y_ub;
    int ey = z_ub/ex;
    assert(ex * ey <= z_ub);
    assert(ex >= ub(xs[0]));
    assert(ey >= ub(xs[1]));
    expl.push(xs[0] > ex);
    expl.push(xs[1] > ey);
  }

  void ex_x_lb(int xi, pval_t pval, vec<clause_elt>& expl) {
    int x_lb = xs[xi].lb_of_pval(pval);
    
    int yi = 1 - xi; 
    int y_ub = ub(xs[yi]);
    int z_lb = lb(z);

    int y_ub0 = ub_0(xs[yi]);
    if(iceil(z_lb, y_ub0) >= x_lb) {
      expl.push(z <= (x_lb-1) * y_ub0);
      return;
    }
    int z_lb0 = lb_0(z);
    if((x_lb-1) * y_ub < z_lb0) {
      expl.push(xs[yi] > iceil(z_lb0-1, x_lb-1));
      return;
    }
    // Choose largest ey s.t. (x_lb-1) * ey < z_lb.
    int ey = (z_lb-1)/(x_lb-1);
    // And smallest ez s.t. (ey * (x_lb-1)) < ez
    int ez = (x_lb-1) * ey + 1;
    assert((x_lb-1) * ey <= ez);
    expl.push(xs[yi] > ey);
    expl.push(z < ez);
  }

  void ex_x_ub(int xi, pval_t pval, vec<clause_elt>& expl) {
    int x_ub = xs[xi].ub_of_pval(pval);
    
    int yi = 1 - xi; 
    int y_lb = lb(xs[yi]);
    int z_ub = ub(z);
    
    int y_lb0 = lb_0(xs[yi]);
    if(y_lb0 > 0 && (x_ub+1) * y_lb0 > z_ub) {
      expl.push(z >= (x_ub+1) * y_lb0);
      return;
    }
    int z_ub0 = ub_0(z);
    if((x_ub+1) * y_lb > z_ub0) {
      expl.push(xs[yi] < iceil(z_ub0+1, x_ub+1));
      return;
    }

    // Pick smallest ey s.t. ((x_ub + 1) * ey) > z_ub.
    int ey = iceil(z_ub+1, x_ub+1);
    int ez = ey * (x_ub+1)-1;
    assert((x_ub+1) * ey > ez);
    expl.push(xs[yi] < ey);
    expl.push(z > ez);
  }

public:
  iprod_nonneg(solver_data* s, patom_t _r, intvar _z, intvar _x, intvar _y)
    : propagator(s), r(_r), z(_z), status(0) {
      assert(s->state.is_entailed_l0(r));
      xs[0] = _x; xs[1] = _y; 

//    fprintf(stderr, "Constructing [iprod_nonneg]\n");
    z.attach(E_LU, watch_callback(wake_default, this, 2));
    for(int ii : irange(2))
      xs[ii].attach(E_LU, watch_callback(wake_default, this, ii));
  }

  bool check_sat(ctx_t& ctx) {
    if(xs[0].ub(ctx) * xs[1].ub(ctx) < z.lb(ctx))
      return false;
    if(z.ub(ctx) < xs[0].lb(ctx) * xs[1].lb(ctx))
      return false;
    return true;
  }
  bool check_unsat(ctx_t& ctx) {
    return !check_sat(ctx);
  }

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cerr << "[[Running iprod(+)]]" << std::endl;
#endif
    int z_low = lb(xs[0]) * lb(xs[1]);
    if(z_low > lb(z)) {
      if(!set_lb(z, z_low, ex_thunk(ex<&P::ex_z_lb>,0, expl_thunk::Ex_BTPRED)))
        return false;
    }
    int z_high = ub(xs[0]) * ub(xs[1]);
    if(z_high < ub(z)) {
      if(!set_ub(z, z_high, ex_thunk(ex<&P::ex_z_ub>,0, expl_thunk::Ex_BTPRED)))
        return false;
    }

    for(int xi : irange(2)) {
      if(ub(xs[1 - xi]) <= 0)
        continue;
      int x_low = iceil(lb(z), ub(xs[1 - xi]));
      if(x_low > lb(xs[xi])) {
        if(!set_lb(xs[xi], x_low, ex_thunk(ex<&P::ex_x_lb>,xi, expl_thunk::Ex_BTPRED)))
          return false;
      }
      int y_lb = lb(xs[1 - xi]);
      if(y_lb > 0) {
        int x_high = ub(z)/lb(xs[1 - xi]);
        if(x_high < ub(xs[xi])) {
          if(!set_ub(xs[xi], x_high, ex_thunk(ex<&P::ex_x_ub>,xi, expl_thunk::Ex_BTPRED)))
            return false;
        }
      }
    }
    return true;
  }

  patom_t r;
  intvar z;
  intvar xs[2];

  char status;
};

// Propagator:
// non-incremental, with naive eager explanations
class iprod : public propagator, public prop_inst<iprod> {
  static watch_result wake_z(void* ptr, int xi) {
    iprod* p(static_cast<iprod*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

  static watch_result wake_xs(void* ptr, int xi) {
    iprod* p(static_cast<iprod*>(ptr)); 
    p->queue_prop();
    return Wt_Keep;
  }

public:
  iprod(solver_data* s, intvar _z, intvar _x, intvar _y)
    : propagator(s), z(_z), x(_x), y(_y)
  {
    z.attach(E_LU, watch_callback(wake_z, this, 0));
    x.attach(E_LU, watch_callback(wake_xs, this, 0));
    y.attach(E_LU, watch_callback(wake_xs, this, 1));
  }
  
  template<class T>
  void push_expl(int_itv iz, int_itv ix, int_itv iy, T& ex) {
    ex.push(z < iz.lb);
    ex.push(z > iz.ub);
    ex.push(x < ix.lb);
    ex.push(x > ix.ub);
    ex.push(y < iy.lb);
    ex.push(y > iy.ub);
  }

  clause* make_expl(int_itv iz, int_itv ix, int_itv iy) {
    expl_builder ex(s->persist.alloc_expl(7)); 
    push_expl(iz, ix, iy, ex);
    return *ex;
  }
  
  bool propagate(vec<clause_elt>& confl) {
    // Non-incremental propagator
#ifdef LOG_PROP
    std::cerr << "[[Running iprod]]" << std::endl;
#endif
    int_itv z_supp(var_unsupp(s, z));          
    int_itv x_supp(var_unsupp(s, x));
    int_itv y_supp(var_unsupp(s, y));

    int_itv z_itv(var_range(s, z));
    int_itv x_itv(var_range(s, x));
    int_itv y_itv(var_range(s, y));
    if(z_itv.elem(0)) {
      if(x_itv.elem(0)) {
        z_supp = int_itv { 0, 0 };
        y_supp = y_itv;
        x_supp = int_itv { 0, 0 };
      }
      if(y_itv.elem(0)) {
        z_supp = int_itv { 0, 0 };
        x_supp = x_itv;
        y_supp |= int_itv { 0, 0 };
      }
    }

    if(x_itv.ub > 0) {
      int_itv x_pos(pos(var_range(s, x)));
      if(y_itv.ub > 0) {
        // + * + 
        int_itv y_pos(pos(var_range(s, y)));
        int_itv xy { x_pos.lb * y_pos.lb, x_pos.ub * y_pos.ub };
        int_itv z_feas(z_itv & xy);
        if(!z_feas.empty()) {
          z_supp |= z_feas;
          // Propagate back to x, y
          x_supp |= (x_itv & int_itv {(z_feas.lb + y_pos.ub - 1)/ y_pos.ub,
                                      z_feas.ub / y_pos.lb});
          y_supp |= (y_itv & int_itv {(z_feas.lb + x_pos.ub - 1) / x_pos.ub,
                                      z_feas.ub / x_pos.lb});
        }
      }
      if(y_itv.lb < 0) {
        // + * -  
        int_itv y_neg(neg(var_range(s, y)));
        int_itv xy { x_pos.ub * y_neg.lb, x_pos.lb * y_neg.ub };
        int_itv z_feas(z_itv & xy);
        if(!z_feas.empty()) {
          z_supp |= z_feas;
          // Propagate back to x, y
          x_supp |= (x_itv & int_itv {z_feas.lb / y_neg.lb,
                                      (z_feas.ub + y_neg.ub + 1)/y_neg.ub});
          y_supp |= (y_itv & int_itv {z_feas.lb / x_pos.lb,
                                      (z_feas.ub - x_pos.ub + 1)/x_pos.ub});
        }
      }
    }
    if(x_itv.lb < 0) {
      int_itv x_neg(neg(var_range(s, x)));
      if(y_itv.ub > 0) {
        // - * +  
        int_itv y_pos(pos(var_range(s, y)));
        int_itv xy { x_neg.lb * y_pos.lb, x_neg.ub * y_pos.lb };
        int_itv z_feas(z_itv & xy);
        if(!z_feas.empty()) {
          z_supp |= z_feas;
          // Propagate back to x, y
          x_supp |= (x_itv & int_itv {z_feas.lb / y_pos.lb,
                                      (z_feas.ub - y_pos.ub + 1)/y_pos.ub});
          y_supp |= (y_itv & int_itv {(z_feas.ub + x_neg.ub + 1)/x_neg.ub,
                                      z_feas.lb / x_neg.lb});
        }
      }
      if(y_itv.lb < 0) {
        // - * - 
        int_itv y_neg(neg(var_range(s, y)));
        int_itv xy { x_neg.ub * y_neg.ub, x_neg.lb * y_neg.lb };
        int_itv z_feas(z_itv & xy);
        if(!z_feas.empty()) {
          z_supp |= z_feas;
          // Propagate back to x, y
          x_supp |= (x_itv & int_itv {z_feas.ub / y_neg.ub,
                                      (z_feas.lb+y_neg.lb+1)/ y_neg.lb});
          y_supp |= (y_itv & int_itv {z_feas.ub / x_neg.ub,
                                      (z_feas.lb+x_neg.lb+1)/ x_neg.lb});
        }
      }
    }

    if(z_supp.ub < z_supp.lb) {
      // Infeasible
      push_expl(z_itv, x_itv, y_itv, confl);
      return false;
    }
    assert(x_supp.lb <= x_supp.ub);
    assert(y_supp.lb <= y_supp.ub);

    if(z_supp.lb > lb(z)) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (z >= z_supp.lb);
      if(!set_lb(z, z_supp.lb, cl))
        return false;
    }
    if(z_supp.ub < ub(z)) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (z <= z_supp.ub);
      if(!set_lb(z, z_supp.lb, cl))
        return false;
    }
    if(x_supp.lb > lb(x)) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (x >= x_supp.lb);
      if(!set_lb(x, x_supp.lb, cl))
        return false;
    }
    if(x_supp.ub < ub(x)) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (x <= x_supp.ub);
      if(!set_ub(x, x_supp.ub, cl))
        return false;
    }
    if(y_supp.lb > lb(y)) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (y >= y_supp.lb);
      if(!set_lb(y, y_supp.lb, cl))
        return false;
    }
    if(y_supp.ub < ub(y)) {
      clause* cl(make_expl(z_itv, x_itv, y_itv));
      (*cl)[0] = (y <= y_supp.ub);
      if(!set_ub(y, y_supp.ub, cl))
        return false;
    }

    return true;
  }

  /*
  bool check_sat(void) {
    return true;
  }
  */

  void root_simplify(void) { }

  void cleanup(void) { is_queued = false; }

protected:
  intvar z;
  intvar x;
  intvar y;
};

irange pos_range(solver_data* s, intvar z) { return irange(std::max(1, (int) z.lb(s)), z.ub(s)+1); }
irange neg_range(solver_data* s, intvar z) { return irange(z.lb(s), std::min(-1, (int) z.ub(s))); }

// Decomposition of z = x * y.
void imul_decomp(solver_data* s, intvar z, intvar x, intvar y) {
  // Establish lower bounds on abs(z).
  // Case splits. x pos:
  if(x.ub(s) > 0) {
    // y pos
    if(y.ub(s) > 0) {
      for(int kx : pos_range(s, x)) {
        for(int ky : pos_range(s, y)) {
          add_clause(s, x < kx, y < ky, z >= kx*ky);  
          add_clause(s, x > kx, y > ky, x < -kx, y < -ky, z <= kx*ky);
        }
      }
    }
    // y neg
    if(y.lb(s) < 0) {
      for(int kx : pos_range(s, x)) {
        for(int ky : neg_range(s, y)) {
          add_clause(s, x < kx, y > ky, z <= kx*ky);
          add_clause(s, x > kx, y < ky, x < -kx, y > -ky, z >= kx*ky);
        }
      }
    }
  }
  // x neg
  if(x.lb(s) < 0) {
    if(y.ub(s) > 0) {
      for(int kx : neg_range(s, x)) {
        for(int ky : pos_range(s, y)) {
          add_clause(s, x > kx, y < ky, z <= kx*ky);
          add_clause(s, x < kx, y > ky, x > -kx, y < -ky, z >= kx*ky);
        }
      }
    }
    if(y.lb(s) < 0) {
      for(int kx : neg_range(s, x)) {
        for(int ky : neg_range(s, y)) {
          add_clause(s, x > kx, y > ky, z >= kx*ky);
          add_clause(s, x < kx, y < ky, x > -kx, y > -ky, z <= kx*ky);
        }
      }
    }
  }
}

class iabs : public propagator, public prop_inst<iabs> {
  watch_result wake(int xi) {
    queue_prop();
    return Wt_Keep;
  }

  void ex_z_lb(int sign, pval_t p, vec<clause_elt>& expl) {
    EX_PUSH(expl, sign ? x < z.lb_of_pval(p) : x > -z.lb_of_pval(p));
  }
  void ex_z_ub(int _xi, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t k(z.ub_of_pval(p));

    EX_PUSH(expl, x > k);
    EX_PUSH(expl, x < -k);
  }

  void ex_lb(int sign, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t k(x.lb_of_pval(p));
    if(sign) {
      // x > -k && z >= k -> x >= k, for some positive k.
      intvar::val_t v = std::max(k, -x.lb(s)+1);
      EX_PUSH(expl, x <= -v);
      EX_PUSH(expl, z < v);
      /*
      intvar::val_t v = std::max(1, k);
      EX_PUSH(expl, x < lb(x));
      EX_PUSH(expl, z < lb(z));
      */
    } else {
      EX_PUSH(expl, z > -k);
    }
  }
  void ex_ub(int sign, pval_t p, vec<clause_elt>& expl) {
    intvar::val_t k(x.ub_of_pval(p));

    if(sign) {
      EX_PUSH(expl, z > k);
    } else {
      intvar::val_t v = k > -1 ? 1 : -k;
      EX_PUSH(expl, x >= v);
      EX_PUSH(expl, z < k);
    }
  }

public:
  iabs(solver_data* s, intvar _z, intvar _x)
    : propagator(s), z(_z), x(_x)
  {
    z.attach(E_LU, watch<&P::wake>(0, Wt_IDEM));
    x.attach(E_LU, watch<&P::wake>(1, Wt_IDEM));
  }
 

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cerr << "[[Running iabs]]" << std::endl;
#endif
    // Case split
    int_itv z_itv { ub(z)+1, lb(z)-1 };
    int_itv x_itv { ub(x)+1, lb(x)-1 };
//    int z_min = ub(z)+1;
//    int z_max = lb(z)-1;

//    int x_min = ub(x)+1;
//    int x_max = lb(x)-1;

    if(lb(x) < 0) {
      int_itv neg { std::max(lb(x), -ub(z)),
                    std::max(ub(x), -lb(z)) };
      if(!neg.empty()) {
        x_itv |= neg;
        z_itv |= -neg;
      }
    }
    if(ub(x) >= 0) {
      int_itv pos { std::max(lb(z), lb(z)),
                    std::min(ub(x), ub(z)) }; 
      if(!pos.empty()) {
        x_itv |= pos;
        z_itv |= pos;
      }
    }

    if(z_itv.ub < ub(z)) {
      if(!set_ub(z, z_itv.ub, expl<&P::ex_z_ub>(0)))
        return false;
    }
    if(z_itv.lb > lb(z)) {
      if(!set_lb(z, z_itv.lb, expl<&P::ex_z_lb>(x_itv.lb >= 0)))
        return false;
    }
    if(x_itv.ub < ub(x)) {
      if(!set_ub(x, x_itv.ub, expl<&P::ex_ub>(x_itv.ub >= 0)))
        return false;
    }
    if(x_itv.lb > lb(x)) {
      if(!set_lb(x, x_itv.lb, expl<&P::ex_lb>(x_itv.lb > 0 , expl_thunk::Ex_BTPRED)))
        return false;
    }
    return true;
#if 0
    int z_min = lb(z);
    if(lb(x) > -z_min) {
      // z = x
      if(z_min > lb(x)) {
        if(!x.set_lb(z_min, expl_thunk ex_x_lb, this, 1))
          return false;
      }
      if(ub(z) < ub(x)) {
         
      }
    } else if(ub(x) < z_min) {
      // z = -x
      
    }
#endif
    return true;
  }

#if 0
  bool check_sat(ctx_t& ctx) {
    int_itv z_itv { z.lb(ctx), z.ub(ctx) };
    if(x.lb(ctx) <= 0) {
      int_itv supp = z_itv & int_itv { std::max((intvar::val_t) 0, -x.ub(ctx)), -x.lb(ctx) };
      if(!supp.empty())
        return true;
    }
    if(x.ub(ctx) >= 0) {
      int_itv supp = z_itv & int_itv { std::max((intvar::val_t) 0, x.lb(ctx)), x.ub(ctx) };
      if(!supp.empty())
        return true;
    }
    return false;
  }
#else
  bool check_sat(ctx_t& ctx) {
    if(x.ub(ctx) < z.lb(ctx)) {
      // Any overlap is non-positive.
      return std::max(-x.ub(ctx), z.lb(ctx)) <= std::min(-x.lb(ctx), z.ub(ctx));
    } else if(-z.lb(ctx) < x.lb(ctx)) {
      // Any overlap is non-negative
      return std::max(x.lb(ctx), z.lb(ctx)) <= std::min(x.ub(ctx), z.ub(ctx));
    } else {
      // Definitely some overlap
      return true;
    }
  }
#endif
  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

  void cleanup(void) { is_queued = false; }

protected:
  intvar z;
  intvar x; 
};

// Only use for small domains
void iabs_decomp(solver_data* s, intvar z, intvar x) {
  // Set up initial bounds
  if(z.lb(s) < 0)
    enqueue(*s, z >= 0, reason());
//    z.set_lb(0, reason());
  if(x.lb(s) < -z.ub(s))
    enqueue(*s, z >= -z.ub(s), reason());
//    x.set_lb(-ub(z), reason());
  if(z.ub(s) < x.ub(s))
    enqueue(*s, x <= z.ub(s), reason());
//    x.set_ub(ub(z), reason());

  for(intvar::val_t k : z.domain(s)) {
    add_clause(s, x < -k, x > k, z <= k);
    add_clause(s, x > -k, z >= k);
    add_clause(s, x < k, z >= k);
  }
}

// Avoids introducing equality lits
#if 0
class ine_bound : public propagator, public prop_inst<ine_bound> {
  enum Vtag { Var_X = 1, Var_Z = 2 };

  static watch_result wake_fix(void* ptr, int k) {
    ine_bound* p(static_cast<ine_bound*>(ptr));
    p->new_fix |= k;
    p->queue_prop();
    return Wt_Keep;
  }

  static watch_result wake_bound(void* ptr, int k) {
    ine_bound* p(static_cast<ine_bound*>(ptr));
    if(p->fixed) 
      p->queue_prop();
    return Wt_Keep;
  }

   watch_result wake_r(int k) {
     if(fixed)
       queue_prop();
     return Wt_Keep;
   }

  static void expl(void* ptr, int xi, pval_t v, vec<clause_elt>& ex) {
    ine_bound* p(static_cast<ine_bound*>(ptr));
    if(xi != 0) {
//      ex.push(p->x != p->lb(x));
      ex.push(p->x < p->lb(x));
      ex.push(p->x > p->ub(x));
    }
    if(xi != 1) {
      // ex.push(p->z != p->lb(z));
      ex.push(p->z < p->lb(z));
      ex.push(p->z > p->lb(z));
    }
    if(xi != 2)
      ex.push(~p->r);
  }

public:
  ine_bound(solver_data* s, intvar _z, intvar _x, patom_t _r)
    : propagator(s), z(_z), x(_x), r(_r),
      fixed(0), new_fix(0) {
    attach(s, r, watch<&P::wake_r>(0));
    z.attach(E_FIX, watch_callback(wake_fix, this, 0));
//    z.attach(E_LU, watch_callback(wake_bound, this, 0));

    x.attach(E_FIX, watch_callback(wake_fix, this, 1));
//    x.attach(E_LU, watch_callback(wake_bound, this, 1));
  }


  inline bool prop_bound(intvar a, intvar b) {
    int k = a.lb(s);
    if(b.lb(s) == k) {
      if(!b.set_lb(k+1, s->persist.create_expl(a < k, a > k, b < k)))
        return false;
    }
    if(b.ub(s) == k) {
      if(!b.set_ub(k-1, s->persist.create_expl(a < k, a > k, b > k)))
        return false;
    }
    return true;
  }

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cout << "[[Running ineq]]" << std::endl;
#endif
    trail_change(s->persist, fixed, (char) (fixed|new_fix));
    
    switch(fixed) {
      case Var_X:
        // return prop_bound(x, z);
        return enqueue(*s, z != lb(x), ex_thunk(expl, 0));
      case Var_Z:
//        return prop_bound(z, x);
        return enqueue(*s, x != lb(z), ex_thunk(expl, 1));
      default:
        if(lb(z) == lb(x)) {
          /*
          int k = lb(z);
          // vec_push(confl, z < k, z > k, x < k, x > k);
          vec_push(confl, z != k, x != k);
          return false;
          */
          return enqueue(*s, ~r, ex_thunk(expl, 2));
        }
        return true;
    }

    return true;
  }

  bool check_sat(ctx_t& ctx) {
    int lb = std::min(z.lb(ctx), x.lb(ctx));
    int ub = std::max(z.ub(ctx), x.ub(ctx));
    return lb < ub;
  }
  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

  void root_simplify(void) { }

  void cleanup(void) {
    new_fix = 0;
    is_queued = false;
  }

protected:
  intvar z;
  intvar x;
  patom_t r;

  // Persistent state
  char fixed;

  // Transient state
  char new_fix;
};

#endif

class ineq : public propagator, public prop_inst<ineq> {
  enum Vtag { Var_X = 1, Var_Z = 2 };
  enum TrigKind { T_Atom, T_Var };
  enum Status { S_None = 0, S_Active = 1 };

  struct trigger {
    TrigKind kind;
    int idx;
  };

  inline bool is_active(trigger t) {
    switch(t.kind) {
      case T_Atom:
        return s->state.is_entailed(r);
      case T_Var:
      default:
        return pred_fixed(s, vs[t.idx].p);
    }
  }

  inline void attach_trigger(trigger t, int ii) {
    switch(t.kind) {
      case T_Atom: 
        attach(s, r, watch<&P::wake_trig>(ii, Wt_IDEM));
        break;
      case T_Var:
        vs[t.idx].attach(E_FIX, watch<&P::wake_trig>(ii, Wt_IDEM));
        break;
    }
  }

  watch_result wake_lb(int wake_gen) {
    if(wake_gen != (int) gen || !(status&S_Active))
      return Wt_Drop;

//    fprintf(stderr, "{%p,lb: %d %d %d\n", this, is_active(trigs[0]), is_active(trigs[1]), is_active(trigs[2]));
    assert(is_active(trigs[1 - active]));
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_ub(int wake_gen) {
    if(wake_gen != (int) gen || !(status&S_Active))
      return Wt_Drop;

//    fprintf(stderr, "{%p,ub: %d %d %d\n", this, is_active(trigs[0]), is_active(trigs[1]), is_active(trigs[2]));
    assert(is_active(trigs[1 - active]));
    queue_prop(); 
    return Wt_Keep;
  }

  inline bool enqueue_trigger(trigger t, int ii, vec<clause_elt>& confl) {
    if(is_active(t)) {
      assert(vs[0].is_fixed(s));
      assert(vs[1].is_fixed(s));
      assert(vs[0].lb(s) == vs[1].lb(s));
      intvar::val_t val = vs[0].lb(s);
      EX_PUSH(confl, ~r);
      confl.push(vs[0] != val);
      confl.push(vs[1] != val);

      /*
      EX_PUSH(confl, vs[0] < val);
      EX_PUSH(confl, vs[0] > val);
      EX_PUSH(confl, vs[1] < val);
      EX_PUSH(confl, vs[1] > val);
      */
      return false; 
    }
    switch(t.kind) {
      case T_Atom:
        return enqueue(*s, ~r, ex_thunk(ex_nil<&P::expl>,ii, expl_thunk::Ex_BTPRED));
      case T_Var:
      {
        intvar::val_t val = vs[1 - t.idx].lb(s);
        prop_val = val;

        if(vs[t.idx].lb(s) == val) {
          return set_lb(vs[t.idx], val+1, ex_thunk(ex_nil<&P::expl_lb>, ii, expl_thunk::Ex_BTPRED));
        }
        if(vs[t.idx].ub(s) == val) {
          return set_ub(vs[t.idx], val-1, ex_thunk(ex_nil<&P::expl_ub>, ii, expl_thunk::Ex_BTPRED));
        }
        // Otherwise, add LB and UB watches
        ++gen;
        trail_change(s->persist, status, (char) S_Active);
        attach(s, vs[t.idx] >= val, watch<&P::wake_lb>(gen, Wt_IDEM));
        attach(s, vs[t.idx] <= val, watch<&P::wake_ub>(gen, Wt_IDEM));
        /*
        return enqueue(*s, vs[t.idx] != val, ex_thunk(ex_nil<&P::expl>,ii)); 
        */
      }
    }
    return true;
  }

  watch_result wake_trig(int wi) {
    assert(is_active(trigs[wi]));
    if(!is_active(trigs[2])) {
      std::swap(trigs[2], trigs[wi]); 
      attach_trigger(trigs[wi], wi);
      return Wt_Drop;
    }
    if(!is_active(trigs[1 - wi]))
      active = 1 - wi;

//    fprintf(stderr, "{%p(%d): %d %d %d\n", this, wi, is_active(trigs[0]), is_active(trigs[1]), is_active(trigs[2]));
    assert(is_active(trigs[1 - active]));
    queue_prop();
    return Wt_Keep;
  }

  void expl(int xi, vec<clause_elt>& ex) {
    trigger t = trigs[active];
    switch(t.kind) {
      case T_Atom:  
        vs[0].explain_eq(lb(vs[0]), ex);
        vs[1].explain_eq(lb(vs[1]), ex);
      /*
        ex.push(vs[0] != vs[0].lb());
        ex.push(vs[1] != vs[1].lb());
        */
        /*
        ex.push(vs[0] < vs[0].lb(s));
        ex.push(vs[0] > vs[0].ub(s));
        ex.push(vs[1] < vs[1].lb(s));
        ex.push(vs[1] > vs[1].ub(s));
        */
        return;
      case T_Var:
        ex.push(~r);
      /*
        ex.push(vs[1 - t.idx] != vs[1 - t.idx].lb());
        */
        /*
        ex.push(vs[1 - t.idx] < vs[1 - t.idx].lb(s));
        ex.push(vs[1 - t.idx] > vs[1 - t.idx].ub(s));
        */
        vs[1-t.idx].explain_eq(lb(vs[1-t.idx]),ex);
        return;
    }
  }

  void expl_lb(int xi, vec<clause_elt>& ex) {
    trigger t = trigs[active];
    ex.push(~r);
    ex.push(vs[t.idx] < prop_val);
    ex.push(vs[1 - t.idx] < prop_val);
    ex.push(vs[1 - t.idx] > prop_val);
    return;
  }

  void expl_ub(int xi, vec<clause_elt>& ex) {
    trigger t = trigs[active];
    ex.push(~r);
    ex.push(vs[t.idx] > prop_val);
    ex.push(vs[1 - t.idx] < prop_val);
    ex.push(vs[1 - t.idx] > prop_val);
    return;
  }

public:
  ineq(solver_data* s, intvar _z, intvar _x, patom_t _r)
    : propagator(s), r(_r), active(0), prop_val(0), gen(0), status(0) {
    vs[0] = _z;
    vs[1] = _x; 

    trigs[0] = { T_Var, 0 };
    trigs[1] = { T_Var, 1 };
    trigs[2] = { T_Atom };

    attach_trigger(trigs[0], 0);
    attach_trigger(trigs[1], 1);
  }


  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cout << "[[Running ineq]]" << std::endl;
#endif
    assert(is_active(trigs[1 - active]));
    assert(is_active(trigs[2]));
    if(vs[0].ub(s) < vs[1].lb(s) || vs[0].lb(s) > vs[1].ub(s))
      return true;
    if(s->state.is_inconsistent(r))
      return true;

    return enqueue_trigger(trigs[active], active, confl);
  }

  void root_simplify(void) { }

  void cleanup(void) {
    is_queued = false;
  }

protected:
  intvar vs[2];
  patom_t r;

  // Persistent state
  trigger trigs[3];
  int active;
  intvar::val_t prop_val;

  unsigned int gen;
  char status;
};

class ineq_s : public propagator, public prop_inst<ineq_s> {
public:
  ineq_s(solver_data* s, intvar z, intvar x, patom_t _r = at_True)
    : propagator(s), r(_r), satisfied(false), fixed(0) {
    assert(ub(r)); // Not already redundant.
    vs[0] = z;
    vs[1] = x;

    z.attach(E_FIX, watch<&P::wake_xs>(0, Wt_IDEM));
    x.attach(E_FIX, watch<&P::wake_xs>(1, Wt_IDEM));
    attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
    attach(s, ~r, watch<&P::wake_nr>(0, Wt_IDEM));
  }

  watch_result wake_r(int _xi) {
    for(int ii : irange(2)) {
      if(is_fixed(vs[ii])) {
        fixed = ii;
        queue_prop();
      }
    }
    return Wt_Keep;
  }

  watch_result wake_nr(int _xi) {
    set(satisfied, (char) true);
    return Wt_Keep;
  }

  void ex_r(int _xi, pval_t _p, vec<clause_elt>& expl) {
    assert(is_fixed(vs[0]) && is_fixed(vs[1]));
    assert(lb(vs[0]) == lb(vs[1]));
    int k = lb(vs[0]);
#if 1
    vs[0].explain_eq(k, expl);
    vs[1].explain_eq(k, expl);
#else
    expl.push(vs[0] < k);
    expl.push(vs[0] > k);
    expl.push(vs[1] < k);
    expl.push(vs[1] > k);
#endif
  }

  void ex_xs(int xi, pval_t _p, vec<clause_elt>& expl) {
    expl.push(~r);
    assert(is_fixed(vs[1-xi]));
    int k = lb(vs[1-xi]);
#if 1
    vs[1-xi].explain_eq(k, expl);
#else
    expl.push(vs[1-xi] < k);
    expl.push(vs[1-xi] > k);
#endif
  }

  watch_result wake_xs(int xi) {
    if(!satisfied) {
      if(in_domain(vs[1-xi], lb(vs[xi]))) {
        fixed = xi;
        queue_prop();
      } else {
        set(satisfied, (char) true);
      }
    }
    return Wt_Keep;
  }

  bool propagate(vec<clause_elt>& confl) {
    if(satisfied)
      return true;
    // Can only happen with first run.
    if(!is_fixed(vs[fixed]))
      return true;

    if(!lb(r)) {
      // Not yet active
      if(!is_fixed(vs[1 - fixed]))
        return true;
      if(lb(vs[0]) == lb(vs[1])) {
        if(!enqueue(*s, ~r, expl<&P::ex_r>(0)))
          return false;
      }
      set(satisfied, (char) true);
      return true;
    }

    // r is enforced.
    int k = lb(vs[fixed]);
    if(in_domain(vs[1-fixed], k)) {
      if(!enqueue(*s, vs[1-fixed] != k, expl<&P::ex_xs>(1-fixed)))
        return false;
    }
    set(satisfied, (char) true);
    return true;
  }

  intvar vs[2];
  patom_t r;
    
  Tchar satisfied;

  int fixed;
};

// Half-reified disequality
bool int_ne(solver_data* s, intvar x, intvar y, patom_t r) {
  intvar::val_t lb = std::max(x.lb(s), y.lb(s));
  intvar::val_t ub = std::min(x.ub(s), y.ub(s));
  if(ub < lb)
    return true;

  if(ub - lb < s->opts.eager_threshold)
  // if(0)
  {
    for(int k : irange(lb, ub+1)) {
      if(!add_clause(s, ~r, x != k, y != k))
        return false;
    }
  } else {
    // return ineq::post(s, x, y, r);
    return ineq_s::post(s, x, y, r);
  }
  return true;
}

#if 1
class pred_le_hr : public propagator, public prop_inst<pred_le_hr> {
  enum { gen_mask = ~(1<<31) };
  enum status { S_Active = 1, S_Red = 2 };
  enum mode { P_None = 0, P_LB = 1, P_UB = 2, P_LU = 3, P_Deact = 4 };

  // Misc helper functions
  inline bool watch_expired(int xi) {
    return ((unsigned int) xi)>>1 != fwatch_gen;
  }
  inline pval_t choose_cut(void) {
    return pred_lb(s, x) + kx + (pred_ub(s, y) + ky - pred_lb(s, x) -kx)/2;
  }
  inline pval_t lb(int pi) { return pred_lb(s, pi); }
  inline pval_t ub(int pi) { return pred_ub(s, pi); }
  // inline spval_t lb(int pi) { return pred_lb(s, pi); }
  // inline spval_t ub(int pi) { return pred_ub(s, pi); }

  // Deactivation triggers
  watch_result wake_fail(int xi) {
    // If this is an expired watch, drop it.
    if(watch_expired(xi)) {
      return Wt_Drop;
    }
    // If the propagator is already enabled,
    // ignore this.
    if(state&S_Active)
      return Wt_Keep;

    // Enqueue the propagator, to set ~r
    if(lb(x) + kx > ub(y) + ky) {
      mode = P_Deact;
      queue_prop();
      return Wt_Keep;
    }
    
    // Otherwise, find replacement watches
    // GKG: What's a good strategy?
    fwatch_gen = (fwatch_gen+1)&gen_mask;
    pval_t cut = choose_cut();
    attach(s, ge_atom(x, cut-kx+1), watch<&P::wake_fail>(fwatch_gen<<1, Wt_IDEM));
    attach(s, le_atom(y, cut-ky-1), watch<&P::wake_fail>((fwatch_gen<<1)|1, Wt_IDEM));
    return Wt_Drop;
  }

  watch_result wake_r(int _xi) {
    if(state & S_Red)
      return Wt_Keep;
    
    // If the constraint is activated, add watches on lb(x) and ub(y).
    if(!attached[0]) {
      s->pred_callbacks[x].push(watch<&P::wake_xs>(0, Wt_IDEM));
      attached[0] = true;
    }
    if(!attached[1]) {
      s->pred_callbacks[y^1].push(watch<&P::wake_xs>(1, Wt_IDEM));
      attached[1] = true;
    }

    trail_change(s->persist, state, (char) S_Active);
    mode = P_LU;
    queue_prop();
    return Wt_Keep;
  }

  watch_result wake_xs(int xi) {
    if(state&S_Red)
      return Wt_Keep;
    // If we've backtracked beyond the activation,
    // drop the watcher.
    if(!(state&S_Active)) {
      attached[xi] = false;
      return Wt_Drop;
    }
    mode |= xi ? P_UB : P_LB; 
    queue_prop();
    return Wt_Keep;
  }

  static void ex_r(void* ptr, int _p, pval_t _val,
    vec<clause_elt>& expl) {
    pred_le_hr* p(static_cast<pred_le_hr*>(ptr));
    vec_push(expl, le_atom(p->x, p->sep-p->kx -1), ge_atom(p->y, p->sep-p->ky));
  }

  static void ex_var(void* ptr, int var,
                        pval_t val, vec<clause_elt>& expl) {
    pred_le_hr* p(static_cast<pred_le_hr*>(ptr));
    expl.push(~(p->r));
    if(var) {
      expl.push(le_atom(p->x, val + p->ky - p->kx - 1));
    } else {
      expl.push(ge_atom(p->y, pval_inv(val) - p->ky + p->kx + 1));
    }
  }
public:
  pred_le_hr(solver_data* s, pid_t _x, pid_t _y, int _k, patom_t _r)
    : propagator(s), r(_r), x(_x), y(_y),
      kx(_k < 0 ? -_k : 0), ky(_k > 0 ? _k : 0),
      fwatch_gen(0),
      mode(P_None), state(0) {
    assert(x < (unsigned int) s->state.p_vals.size());
    assert(y < (unsigned int) s->state.p_vals.size());
    /*
    s->pred_callbacks[x].push(watch<&P::wake_xs>(0, Wt_IDEM));
    s->pred_callbacks[y^1].push(watch<&P::wake_xs>(1, Wt_IDEM));
    */
    // Pick an initial cut
//    x.attach(E_LB, watch_callback(wake_xs, this, 0, 1));
//    y.attach(E_UB, watch_callback(wake_xs, this, 1, 1));
    attached[0] = false; attached[1] = false;
    pval_t cut = choose_cut();
    attach(s, ge_atom(x, cut), watch<&P::wake_fail>(fwatch_gen<<1, Wt_IDEM));
    attach(s, le_atom(y, cut), watch<&P::wake_fail>((fwatch_gen<<1)|1, Wt_IDEM));

    attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
  }
  
  /*
  forceinline pval_t lb(pid_t p) { return s->state.p_vals[p]; }
  forceinline pval_t ub(pid_t p) { return pval_inv(s->state.p_vals[p^1]); }
  */
  
  bool propagate(vec<clause_elt>& confl) {
    // Non-incremental propagator
#ifdef LOG_PROP
    std::cerr << "[[Running ile]]" << std::endl;
#endif
    if(state&S_Red)
      return true;

    if(mode&P_Deact) {
      // Deactivation
      sep = pred_lb(s, x) + kx;
      assert(sep > pred_ub(s, y) + ky);
      if(!enqueue(*s, ~r, ex_thunk(ex_r, 0))) {
        return false;
      }
      trail_change(s->persist, state, (char) S_Red);
      return true;
    }

    if(!(state&S_Active))
      return true;

    assert(s->state.is_entailed(r));

    if(mode&P_LB) {
      // FIXME: Overflow problems abound
      if(lb(x) + kx > lb(y) + ky) {
        if(!enqueue(*s, ge_atom(y, lb(x) + kx - ky), expl_thunk { ex_var, this, 1 }))
          return false;
      }
    }
    if(mode&P_UB) {
      if(ub(y) + ky < ub(x) + kx) {
        if(!enqueue(*s, le_atom(x, ub(y) + ky - kx), expl_thunk { ex_var, this, 0}))
          return false;
      }
    }
    return true;
  }

  void root_simplify(void) {
    if(ub(x) + kx <= lb(y) + ky || s->state.is_inconsistent(r)) {
      state = S_Red;
      return;
    }

    if(s->state.is_entailed(r)) {
      // FIXME: Instead, disable the propagator
      // and swap in a pred_le builtin.
      state = S_Active; 
    }
  }

  void cleanup(void) { mode = P_None; is_queued = false; }

protected:
  // Parameters
  patom_t r;
  pid_t x;
  pid_t y;
  pval_t kx;
  pval_t ky;

  // Transient bookkeeping
  unsigned int fwatch_gen; // For watch expiration
  pval_t sep; // For explanation
  bool attached[2];

  // Persistent state
  char mode;
  char state;

};
#else
class pred_le_hr : public propagator, public prop_inst<pred_le_hr> {
  enum status { S_None = 0, S_Active = 1, S_Red = 2 };
  enum mode { P_LB = 1, P_UB = 2, P_LU = 3 };

  inline pval_t lb(int pi) { return pred_lb(s, pi); }
  inline pval_t ub(int pi) { return pred_ub(s, pi); }

  watch_result wake_r(int _xi) {
    if(state&S_Red)
      return Wt_Keep;
    
    set(status, (char) S_Active);
    if(lb(y) + ky < lb(x) + kx) {
      mode |= P_LB;
      queue_prop();
    }
    if(ub(y) + ky < ub(x) + kx) {
      mode |= P_UB;
      queue_prop();
    }
    return Wt_Keep;
  }

  watch_result wake_x(int xi) {
    if(state&S_Red)
      return Wt_Keep;
    
    pval_t vx = lb(x);
    pval_t vy = (status&S_Active) ? pred_lb(y) : pred_ub(y);
    if(pred_lb(s, x) + kx > pred_lb(s, y) + ky) {
      queue_prop();
    }
    return Wt_Keep;
  }

  void ex_r(int _p, pval_t _val, vec<clause_elt>& expl) {
    vec_push(expl, le_atom(x, sep-p->kx - 1), ge_atom(y, sep-p->ky));
  }

  void ex_var(int var, pval_t val, vec<clause_elt>& expl) {
    expl.push(~r);
    if(var) {
      expl.push(le_atom(x, val + ky - kx - 1));
    } else {
      expl.push(ge_atom(y, pval_inv(val) - ky + kx + 1));
    }
  }
public:
  pred_le_hr(solver_data* s, pid_t _x, pid_t _y, int _k, patom_t _r)
    : propagator(s), r(_r), x(_x), y(_y),
      kx(_k < 0 ? -_k : 0), ky(_k > 0 ? _k : 0),
      fwatch_gen(0),
      mode(P_None), state(0) {
    assert(x < s->state.p_vals.size());
    assert(y < s->state.p_vals.size());

    s->pred_callbacks[x].push(watch<&P::wake_xs>(0, Wt_IDEM));
    s->pred_callbacks[y^1].push(watch<&P::wake_xs>(1, Wt_IDEM));

    attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
  }
  
  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cerr << "[[Running ile]]" << std::endl;
#endif
    if(state&S_Red)
      return true;

    if(pred_lb(s, x) + kx > pred_ub(s, y) + ky) {
      if(!enqueue(*s, ~r, ex_thunk(ex<&P::ex_r>, 0)))
        return false;
      set(state, (char) S_Red);
      return true;
    }
    if(mode&P_Deact) {
      // Deactivation
      sep = pred_lb(s, x) + kx;
      assert(sep > pred_ub(s, y) + ky);
      if(!enqueue(*s, ~r, ex_thunk(ex_r, 0))) {
        return false;
      }
      trail_change(s->persist, state, (char) S_Red);
      return true;
    }

    if(!(state&S_Active))
      return true;

    assert(s->state.is_entailed(r));

    if(mode&P_LB) {
      // FIXME: Overflow problems abound
      if(lb(x) + kx > lb(y) + ky) {
        if(!enqueue(*s, ge_atom(y, lb(x) + kx - ky), expl_thunk { ex_var, this, 1 }))
          return false;
      }
    }
    if(mode&P_UB) {
      if(ub(y) + ky < ub(x) + kx) {
        if(!enqueue(*s, le_atom(x, ub(y) + ky - kx), expl_thunk { ex_var, this, 0}))
          return false;
      }
    }
    return true;
  }

  void root_simplify(void) {
    if(ub(x) + kx <= lb(y) + ky || s->state.is_inconsistent(r)) {
      state = S_Red;
      return;
    }

    if(s->state.is_entailed(r)) {
      // FIXME: Instead, disable the propagator
      // and swap in a pred_le builtin.
      state = S_Active; 
    }
  }

  void cleanup(void) { mode = P_None; is_queued = false; }

protected:
  // Parameters
  patom_t r;
  pid_t x;
  pid_t y;
  pval_t kx;
  pval_t ky;

  // Transient bookkeeping
  Tchar state;
};
#endif
class int_le_hr : public propagator, public prop_inst<int_le_hr> {
  enum Status { S_None = 0, S_Active = 1, S_Red = 2 };
  enum Change { C_None = 0, C_LB = 1, C_UB = 2, C_DIS = 4 };
  
  watch_result wake_r(int _k) {
    set(status, (char) S_Active);
    if(lb(x) > lb(y)) {
      change |= C_LB;
      queue_prop();
    }
    if(ub(y) < ub(x)) {
      change |= C_UB;
      queue_prop();
    }
    return Wt_Keep;
  }
  watch_result wake_lb(int _xi) {
    if(status&S_Red)
      return Wt_Keep;
    if(status&S_Active) {
      if(lb(x) > lb(y)) {
        change |= C_LB;
        queue_prop();
      }
    } else {
      if(lb(x) > ub(y)) {
        change |= C_DIS;
        cut = lb(x);
        queue_prop();
      }
    }
    return Wt_Keep;
  }
  watch_result wake_ub(int _xi) {
    if(status&S_Red)
      return Wt_Keep;
    if(status&S_Active) {
      if(ub(y) < ub(x)) {
        change |= C_UB;
        queue_prop();
      }
    } else {
      if(ub(y) < lb(x)) {
        change |= C_DIS;
        cut = lb(x);
        queue_prop();
      }
    }
    return Wt_Keep;
  }

  void ex_lb(int _xi, pval_t p, vec<clause_elt>& expl) {
    int y_lb = y.lb_of_pval(p);
    expl.push(~r);
    expl.push(x < y_lb);
  }
  void ex_ub(int _xi, pval_t p, vec<clause_elt>& expl) {
    int x_ub = x.ub_of_pval(p);
    expl.push(~r);
    expl.push(y > x_ub);
  }
  void ex_r(int _xi, pval_t _p, vec<clause_elt>& expl) {
    expl.push(x < cut);
    expl.push(y >= cut);
  }

public:
  int_le_hr(solver_data* s, patom_t _r, intvar _x, intvar _y)
    : propagator(s), r(_r), x(_x), y(_y), change(C_None), status(S_None) {
    
    assert(!s->state.is_inconsistent(r)); 

    x.attach(E_LB, watch<&P::wake_lb>(0, Wt_IDEM));
    y.attach(E_UB, watch<&P::wake_ub>(0, Wt_IDEM));

    if(s->state.is_entailed(r)) {
      status = S_Active;
    } else {
      attach(s, r, watch<&P::wake_r>(0, Wt_IDEM)); 
    }
  }

  bool check_sat(ctx_t& ctx) {
    return !r.lb(ctx) || x.lb(ctx) <= y.ub(ctx);
  }
  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

  bool propagate(vec<clause_elt>& confl) {
    if(status&S_Red)
      return true;
    
    if(change&C_DIS) {
      if(!enqueue(*s, ~r, ex_thunk(ex<&P::ex_r>,0)))
        return false;
      set(status, (char) S_Red);
    }
    if(change&C_LB) {
      if(!set_lb(y, lb(x),
          ex_thunk(ex<&P::ex_lb>,0)))
        return false;
    }
    if(change&C_UB) {
      if(!set_ub(x, ub(y),
          ex_thunk(ex<&P::ex_ub>,0)))
        return false;
    }
    change = C_None;
    return true;
  }

  void cleanup(void) {
    is_queued = false;
    change = C_None;
  }

  patom_t r;
  intvar x;
  intvar y;

  char change;
  int cut;
  Tchar status;
};

class int_eq_hr : public propagator, public prop_inst<int_eq_hr> {
  enum Status { S_None = 0, S_Active = 1, S_Red = 2 };
  enum Change { C_None = 0, C_LB = 1, C_UB = 2, C_DIS = 4 };
  
  watch_result wake_r(int _k) {
    set(status, (char) S_Active);
    if(lb(xs[0]) != lb(xs[1])) {
      change |= C_LB;
      lb_var = lb(xs[0]) < lb(xs[1]) ? 1 : 0;
      queue_prop();
    }
    if(ub(xs[0]) != ub(xs[1])) {
      change |= C_UB;
      ub_var = ub(xs[0]) < ub(xs[1]) ? 0 : 1;
      queue_prop();
    }
    return Wt_Keep;
  }
  watch_result wake_lb(int xi) {
    if(status&S_Red)
      return Wt_Keep;
    if(status&S_Active) {
      if(lb(xs[xi]) > lb(xs[xi^1])) {
        lb_var = xi;
        change |= C_LB;
        queue_prop();
      }
    } else {
      if(lb(xs[xi]) > ub(xs[xi^1])) {
        change |= C_DIS;
        cut = lb(xs[xi]);
        queue_prop();
      }
    }
    return Wt_Keep;
  }
  watch_result wake_ub(int xi) {
    if(status&S_Red)
      return Wt_Keep;
    if(status&S_Active) {
      if(ub(xs[xi]) < ub(xs[xi^1])) {
        ub_var = xi;
        change |= C_UB;
        queue_prop();
      }
    } else {
      if(ub(xs[xi]) < lb(xs[xi^1])) {
        change |= C_DIS;
        cut = lb(xs[xi^1]);
        queue_prop();
      }
    }
    return Wt_Keep;
  }

  void ex_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    int x_lb = xs[xi].lb_of_pval(p);
    expl.push(~r);
    expl.push(xs[xi^1] < x_lb);
  }
  void ex_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    int x_ub = xs[xi].ub_of_pval(p);
    expl.push(~r);
    expl.push(xs[xi^1] > x_ub);
  }
  void ex_r(int _xi, pval_t _p, vec<clause_elt>& expl) {
    if(lb(xs[0]) < cut) {
      expl.push(xs[0] >= cut);
      expl.push(xs[1] < cut);
    } else {
      expl.push(xs[0] < cut);
      expl.push(xs[1] >= cut);
    }
  }

public:
  int_eq_hr(solver_data* s, patom_t _r, intvar x, intvar y)
    : propagator(s), r(_r), change(C_None), status(S_None) {
    xs[0] = x;
    xs[1] = y;
    
    assert(!s->state.is_inconsistent(r)); 

    for(int ii = 0; ii < 2; ii++) {
      xs[ii].attach(E_LB, watch<&P::wake_lb>(ii, Wt_IDEM));
      xs[ii].attach(E_UB, watch<&P::wake_ub>(ii, Wt_IDEM));
    }
    if(s->state.is_entailed(r)) {
      status = S_Active;
    } else {
      attach(s, r, watch<&P::wake_r>(0, Wt_IDEM)); 
    }
  }

  bool propagate(vec<clause_elt>& confl) {
    if(status&S_Red)
      return true;
    
    if(change&C_DIS) {
      if(!enqueue(*s, ~r, ex_thunk(ex<&P::ex_r>,0)))
        return false;
      set(status, (char) S_Red);
    }
    if(change&C_LB) {
      if(!set_lb(xs[lb_var^1], lb(xs[lb_var]),
          ex_thunk(ex<&P::ex_lb>,lb_var^1)))
        return false;
    }
    if(change&C_UB) {
      if(!set_ub(xs[ub_var^1], ub(xs[ub_var]),
          ex_thunk(ex<&P::ex_ub>,ub_var^1)))
        return false;
    }
    change = C_None;
    return true;
  }

  void cleanup(void) {
    is_queued = false;
    change = C_None;
  }

  patom_t r;
  intvar xs[2];

  char change;
  int lb_var; int ub_var;
  int cut;
  Tchar status;
};

/* // TODO
class int_eq_hr_dom : public propagator, public prop_inst<int_eq_hr_dom> {
  watch_result wake_rem(int vi) {
    if(supports.support() != (vi>>1)) {
      watched[vi] = false; 
      return Wt_Drop;
    }
    // Try to find a replacement
    if(replace_support())
      return Wt_Drop;
    queue_prop();
    return Wt_Keep;
  }
public:
  int_eq_hr_dom(solver_data* s, intvar _x, intvar _y, patom_t _r)
    : x(_x), y(_y), r(_r) {
  }

  bool replace_support(void) {
    if(supports.replace_support(s,
      [&](unsigned int vi) {
        int k = vals[vi];
        return in_domain(x, k) && in_domain(y, k); })) {
      // Found replaced support
    }
  }
  vec<int> vals;
  
  support_list<unsigned int> supports;
  // Has size 2 * vals.size(), to track which
  // (arg, val) pairs already have watches.
  vec<bool> watched;
};
*/

bool int_eq(solver_data* s, intvar x, intvar y, patom_t r) {
  if(s->state.is_inconsistent(r))
    return true;
  // new int_eq_hr(s, r, x, y);
  // return true;
  return int_eq_hr::post(s, r, x, y);
}

class pred_le_hr_s : public propagator, public prop_inst<pred_le_hr_s> {
  enum status { S_Active = 1, S_Red = 2 };
  enum mode { P_None = 0, P_LB = 1, P_UB = 2, P_LU = 3, P_Deact = 4 };

  inline pval_t lb(int pi) { return pred_lb(s, pi); }
  inline pval_t ub(int pi) { return pred_ub(s, pi); }

  watch_result wake_r(int _xi) {
    if(state & S_Red)
      return Wt_Keep;
    
    trail_change(s->persist, state, (char) S_Active);
    mode = P_LU;
    queue_prop();
    return Wt_Keep;
  }
  watch_result wake_red(int _xi) {
    trail_change(s->persist, state, (char) S_Red);
    return Wt_Keep;
  }

  watch_result wake_xs(int xi) {
    if(state&S_Red)
      return Wt_Keep;

    if(xi) {
      if(pred_ub(s, y) + ky < pred_ub(s, x) + kx) {
        mode |= P_UB;
        queue_prop();
      }
    } else {
      if(pred_lb(s, x) + kx > pred_lb(s, y) + ky) {
        mode |= P_LB;
        queue_prop();
      }
    }
    return Wt_Keep;
  }

  static void ex_r(void* ptr, int _x, pval_t p, vec<clause_elt>& elt) {
    return static_cast<P*>(ptr)->ex_r(_x, p, elt);
  }
  void ex_r(int _p, pval_t _val,
    vec<clause_elt>& expl) {
    vec_push(expl, le_atom(x, sep-kx -1), ge_atom(y, sep-ky));
  }

  static void ex_var(void* ptr, int x, pval_t p, vec<clause_elt>& elt) {
    return static_cast<P*>(ptr)->ex_var(x, p, elt);
  }
  void ex_var(int var, pval_t val, vec<clause_elt>& expl) {
    expl.push(~r);
    if(var) {
      expl.push(le_atom(x, val + ky - kx - 1));
    } else {
      expl.push(ge_atom(y, pval_inv(val) - ky + kx + 1));
    }
  }
public:
  pred_le_hr_s(solver_data* s, pid_t _x, pid_t _y, int _k, patom_t _r)
    : propagator(s), r(_r), x(_x), y(_y),
      kx(_k < 0 ? -_k : 0), ky(_k > 0 ? _k : 0),
      mode(P_None), state(0) {
    assert(x < (unsigned int) s->state.p_vals.size());
    assert(y < (unsigned int) s->state.p_vals.size());
    s->pred_callbacks[x].push(watch<&P::wake_xs>(0, Wt_IDEM));
    s->pred_callbacks[y^1].push(watch<&P::wake_xs>(1, Wt_IDEM));

    attach(s, r, watch<&P::wake_r>(0, Wt_IDEM));
    attach(s, ~r, watch<&P::wake_red>(0, Wt_IDEM));
  }
  
  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cerr << "[[Running ile_s]]" << std::endl;
#endif
    if(state&S_Red)
      return true;

    // if(mode&P_Deact) {
    if(pred_lb(s, x) + kx > pred_ub(s, y) + ky) {
      // Deactivation
      sep = pred_lb(s, x) + kx;
      assert(sep > pred_ub(s, y) + ky);
      if(!enqueue(*s, ~r, ex_thunk(ex_r, 0))) {
        return false;
      }
      trail_change(s->persist, state, (char) S_Red);
      return true;
    }

    if(!(state&S_Active))
      return true;

    assert(s->state.is_entailed(r));

    if(mode&P_LB) {
      // FIXME: Overflow problems abound
      if(lb(x) + kx > lb(y) + ky) {
        if(!enqueue(*s, ge_atom(y, lb(x) + kx - ky), expl_thunk { ex_var, this, 1 }))
          return false;
      }
    }
    if(mode&P_UB) {
      if(ub(y) + ky < ub(x) + kx) {
        if(!enqueue(*s, le_atom(x, ub(y) + ky - kx), expl_thunk { ex_var, this, 0}))
          return false;
      }
    }
    return true;
  }

  void root_simplify(void) {
    if(ub(x) + kx <= lb(y) + ky || s->state.is_inconsistent(r)) {
      state = S_Red;
      return;
    }

    if(s->state.is_entailed(r)) {
      // FIXME: Instead, disable the propagator
      // and swap in a pred_le builtin.
      state = S_Active; 
    }
  }

  void cleanup(void) { mode = P_None; is_queued = false; }

protected:
  // Parameters
  patom_t r;
  pid_t x;
  pid_t y;
  pval_t kx;
  pval_t ky;

  pval_t sep;

  // Persistent state
  char mode;
  char state;
};


/*
class ile_hr : public propagator {
  enum status { S_Active = 1, S_Red = 2 };

  static void wake_r(void* ptr, int _xi) {
    ile_hr* p(static_cast<ile_hr*>(ptr));
    if(p->state & S_Red)
      return;
    trail_change(p->s->persist, p->state, (char) S_Active);
    p->queue_prop();
  }

  static void wake_xs(void* ptr, int xi) {
    ile_hr* p(static_cast<ile_hr*>(ptr));
    if(p->state&S_Red)
      return;
    p->queue_prop();
  }

  static void ex_r(void* ptr, int sep, pval_t _val,
    vec<clause_elt>& expl) {
    ile_hr* p(static_cast<ile_hr*>(ptr));
    vec_push(expl, p->x < sep, p->y >= sep - p->k);
  }

  static void ex_var(void* ptr, int var,
                        pval_t val, vec<clause_elt>& expl) {
    ile_hr* p(static_cast<ile_hr*>(ptr));
    expl.push(~(p->r));
    if(var) {
      expl.push(p->x > to_int(val) + p->k);
    } else {
      expl.push(p->y < to_int(pval_inv(val)) - p->k);
    }
  }
public:
  ile_hr(solver_data* s, intvar _x, intvar _y, int _k, patom_t _r)
    : propagator(s), r(_r), x(_x), y(_y), k(_k) {
    x.attach(E_LB, watch_callback(wake_xs, this, 0, 1));
    y.attach(E_UB, watch_callback(wake_xs, this, 1, 1));
    attach(s, r, watch_callback(wake_r, this, 0, 1));
  }
  
  bool propagate(vec<clause_elt>& confl) {
    // Non-incremental propagator
#ifdef LOG_ALL
    std::cerr << "[[Running ile]]" << std::endl;
#endif
    if(state & S_Active) {
      if(lb(x) > lb(y) + k) {
        if(!y.set_lb(lb(x) - k, expl_thunk { ex_var, this, 1 }))
          return false;
      }
      if(ub(y) + k < ub(x)) {
        if(!x.set_ub(ub(y) + k, expl_thunk { ex_var, this, 0}))
          return false;
      }
    } else {
      if(lb(x) > ub(y) + k) {
        if(!enqueue(*s, ~r, expl_thunk { ex_r, this, (int) lb(x) }))
          return false;
        trail_change(s->persist, state, (char) S_Red);
      }
    }
    return true;
  }

  void root_simplify(void) {
    if(ub(x) <= lb(y) + k || s->state.is_inconsistent(r)) {
      state = S_Red;
      return;
    }

    if(s->state.is_entailed(r)) {
      state = S_Active; 
    }
  }

  void cleanup(void) { is_queued = false; }

protected:
  // Parameters
  patom_t r;
  intvar x;
  intvar y;
  int k;

  // Persistent state
  char state;
};
*/

bool pred_leq(solver_data* s, pid_t x, pid_t y, int k) {
  if(pred_ub(s, y) + k < pred_lb(s, x))
    return false;

  if(!enqueue(*s, ge_atom(y, pred_lb(s, x) - k), reason()))
    return false;
  if(!enqueue(*s, le_atom(x, pred_ub(s, y) + k), reason()))
    return false;

  s->infer.pred_ineqs[x].push({y, k});
  s->infer.pred_ineqs[y^1].push({x^1, k});
  return true;
}

bool int_leq(solver_data* s, intvar x, intvar y, int k) {
#ifdef USE_DIFFLOGIC
  if(s->opts.global_diff)
    return difflogic::post(s, at_True, x, y, k);
#endif
  return pred_leq(s, x.p, y.p, k + y.off - x.off);

  /*
  if(ub(y) + k < lb(x))
    return false;
  
  if(!enqueue(*s, y >= lb(x) - k, reason()))
    return false;
  if(!enqueue(*s, x <= ub(y) + k, reason()))
    return false;

  pid_t px = x.pid;
  pid_t py = y.pid;  
  s->infer.pred_ineqs[px].push({py, k});
  s->infer.pred_ineqs[py^1].push({px^1, k});
  return true;
  */
}

bool int_le(solver_data* s, intvar x, intvar y, int k, patom_t r) {
  if(s->state.is_inconsistent(r))
    return true;
  if(s->state.is_entailed(r) && y.ub(s) + k < x.lb(s))
    return false;

#ifdef USE_DIFFLOGIC
  if(s->opts.global_diff)
    return difflogic::post(s, r, x, y, k);
#endif
  if(s->state.is_entailed(r))
    return int_leq(s, x, y, k);

  /*
  new pred_le_hr_s(s, x.p, y.p, k, r);
  // new int_le_hr(s, r, x, y+k);
  return true;
  */
  // return pred_le_hr::post(s, x.p, y.p, k - x.off + y.off, r);
  // return pred_le_hr_s::post(s, x.p, y.p, k - x.off + y.off, r);
  return int_le_hr::post(s, r, x, y + k);
}

bool pred_le(solver_data* s, pid_t x, pid_t y, int k, patom_t r) {
  if(s->state.is_inconsistent(r))
    return true;
  if(s->state.is_entailed(r))
    return pred_leq(s, x, y, k);
  pval_t lb = std::max(pred_lb(s, x), pred_lb(s, y)+k);
  pval_t ub = std::min(pred_ub(s, x), pred_ub(s, y)+k);

  if(ub < lb) {
    if(pred_lb(s, x) > pred_ub(s, y) + k)
      return enqueue(*s, ~r, reason());
    return true;
  }

  if(ub - lb < (unsigned int) s->opts.eager_threshold)
  // if(0)
  {
    if(pred_lb(s, y)+k < lb) {   
      if(!add_clause(s, ~r, ge_atom(y, lb-k)))
        return false;
    }
    if(pred_ub(s, x) > ub) {
      if(!add_clause(s, ~r, le_atom(x, ub)))
        return false;
    }
    for(pval_t v = lb; v < ub; ++v) {
      if(!add_clause(s, ~r, le_atom(x, v), ge_atom(y, v-k+1)))
        return false;
    }
  } else {
    // new pred_le_hr(s, x, y, k, r);
    // new pred_le_hr_s(s, x, y, k, r);
    return pred_le_hr_s::post(s, x, y, k, r);
  }
  return true;
}

// r -> (z = abs(x))
bool int_abs(solver_data* s, intvar z, intvar x, patom_t r) {
  // iabs_decomp(s, z, x);
  if(!s->state.is_entailed_l0(r))
    GEAS_WARN("Half-reified int_abs not yet implemented.");

  if(z.lb(s) < 0) {
    if(!enqueue(*s, z >= 0, reason ()))
      return false;
  }
  if(z.ub(s) < x.ub(s)) {
    if(!enqueue(*s, x <= z.ub(s), reason ()))
      return false;
  }
  return iabs::post(s, z, x);
/*
  */
  // x <= z
  /*
  pred_le(s, x.pid^1, z.pid, -IVAR_INV_OFFSET, at_True);
  pred_le(s, z.pid, x.pid^1, IVAR_INV_OFFSET, at_True);
  */
#if 0
  pred_le(s, x.p, z.p, z.off - x.off, at_True);
  // (WARNING: Offsets here are fragile wrt offset changes)
  // (-x) <= z
  pred_le(s, x.p^1, z.p, -IVAR_INV_OFFSET + z.off + x.off, at_True);

  // x >= 0 -> (z <= x)
  pred_le(s, z.p, x.p, 0 + x.off - z.off, x >= 0);
  // x <= 0 -> (z <= -x)
  if(!enqueue(*s, x <= z.ub(s), reason ()))
     return false;
   /*
   pred_le(s, x.pid^1, z.pid, -IVAR_INV_OFFSET, at_True);
   pred_le(s, z.pid, x.pid^1, IVAR_INV_OFFSET, at_True);
   */
  pred_le(s, x.p, z.p, 0 + z.off - x.off, at_True);
  // (WARNING: Offsets here are fragile wrt offset changes)
  // (-x) <= z
  pred_le(s, x.p^1, z.p, -IVAR_INV_OFFSET + z.off + x.off, at_True);

  // x >= 0 -> (z <= x)
  pred_le(s, z.p, x.p, 0 + x.off - z.off, x >= 0);
  // x <= 0 -> (z <= -x)
  pred_le(s, z.p, x.p^1, IVAR_INV_OFFSET - x.off - z.off, x <= 0);
  return true;
#else
  /*
  if(!enqueue(*s, x <= z.ub(s), reason ()))
    return false;
    */
  return int_le(s, x, z, 0, r)
    && int_le(s, -x, z, 0, r)
    && int_le(s, z, x, 0, x >= 0)
    && int_le(s, z, -x, 0, x <= 0);
#endif
}

bool is_binary(solver_data* s, intvar x) { return x.lb(s) == 0 && x.ub(s) == 1; }

bool mul_bool(solver_data* s, intvar z, intvar x, patom_t y) {
  if(!add_clause(s, y, z == 0))
    return false;

  return int_le(s, z, x, 0, x.lb(s) >= 0 ? at_True : y)
    && int_le(s, x, z, 0, x.ub(s) <= 0 ? at_True : y);
}

#if 0
class isquare : public propagator, public prop_inst<isquare> {
  watch_result wake_x(int xi) {
    queue_prop();
    return  Wt_Keep;
  }


  isquare(solver_data* _s, intvar _z, intvar _x)
    : s(_s), z(_z), x(_x) {
      if(lb(z) < 0)
        set_lb(z, 0, reason());
      if(lb(x) >= 0) {
        if(lb(z) < lb(x) * lb(x)) {
          set_lb(z, lb(x) * lb(x), reason());
        }
        if(ub(z) > ub(x) * ub(x)) {
          set_ub(x, 
  }

  void expl_z(int xi, pval_t pval, vec<clause_elt>& expl) {
    if(!xi) {
      // lb(z)
      intvar::val_t v = std::max(1, to_int(pval));
    }
  }
  bool propagate(void) {

  }

  void cleanup(void) { changes = 0; is_queued = false; }

  char changes;
}
#endif

bool square_decomp(solver_data* s, intvar z, intvar x) {
  vec<intvar::val_t> abs_vals;
  vec<intvar::val_t> z_vals;
  for(intvar::val_t v : x.domain(s)) {
    z_vals.push(v*v);
    if(v < 0)
      abs_vals.push(-v);
    else
      abs_vals.push(v);
  }
  make_sparse(z, z_vals);

  uniq(abs_vals);
  for(intvar::val_t v : abs_vals) {
    if(!add_clause(s, z > v*v, x <= v))
      return false;
    if(!add_clause(s, z > v*v, x >= -v))
      return false;
    if(!add_clause(s, z < v*v, x <= -v, x >= v))
      return false;
  }
  return true;
}

bool int_mul(solver_data* s, intvar z, intvar x, intvar y, patom_t r) {
  if(!s->state.is_entailed_l0(r))
    GEAS_WARN("Half-reified int_mul not yet implemented.");

  if(is_binary(s, x)) {
    return mul_bool(s, z, y, x >= 1);
  } else if(is_binary(s, y)) {
    return mul_bool(s, z, x, y >= 1);
  }

  if(x.p == y.p) {
    if(x.ub(s) - x.lb(s) < s->opts.eager_threshold) {
      return square_decomp(s, z, x);
    }
  }

  // imul_decomp(s, z, x, y);
  if(z.lb(s) >= 0) {
    if(x.lb(s) >= 0 || y.lb(s) >= 0) {
      // new iprod_nonneg(s, r, z, x, y);
      // return true;
      return iprod_nonneg::post(s, r, z, x, y);
    } else if(x.ub(s) <= 0) {
      // new iprod_nonneg(s, r, z, -x, y);
      // return true;
      return iprod_nonneg::post(s, r, z, -x, y);
    } else if(y.ub(s) <= 0) {
      // new iprod_nonneg(s, r, z, x, -y);
      // return true;
      return iprod_nonneg::post(s, r, z, x, -y);
    }
  } else if(z.ub(s) <= 0) {
    if(x.lb(s) >= 0 || y.ub(s) <= 0) {
      // new iprod_nonneg(s, r, -z, x, -y);
      // return true;
      return iprod_nonneg::post(s, r, -z, x, -y);
    }  else if(x.ub(s) <= 0 || y.lb(s) >= 0) {
      // new iprod_nonneg(s, r, -z, -x, y);
      // return true;
      return iprod_nonneg::post(s, r, -z, -x, y);
    } 
  }
  // new iprod(s, z, x, y);
  // return true;
  return iprod::post(s, z, x, y);
}

// z = x div k. k must be strictly positive.
class idiv_xk : public propagator, public prop_inst<idiv_xk> {
  void ex_z_lb(int _xi, pval_t p, vec<clause_elt>& expl) {
    int zlb = z.lb_of_pval(p);
    expl.push(x < k * zlb);
  }
  void ex_z_ub(int _xi, pval_t p, vec<clause_elt>& expl) {
    int zub = z.ub_of_pval(p);
    expl.push(x >= k * (zub + 1));
  }
  void ex_x_lb(int _xi, pval_t p, vec<clause_elt>& expl) {
    int xlb = x.lb_of_pval(p);
    EX_PUSH(expl, z <= (xlb - 1)/k);
  }
  void ex_x_ub(int _xi, pval_t p, vec<clause_elt>& expl) {
    int xub = x.ub_of_pval(p);
    EX_PUSH(expl, z >= (xub + 1)/k);
  }

  watch_result wake(int xi) {
    if(xi)
      z_change = true;
    else
      x_change = true;
    queue_prop();
    return Wt_Keep;
  }

public:
  idiv_xk(solver_data* s, intvar _z, intvar _x, int _k) 
    : propagator(s), z(_z), x(_x), k(_k) {
    x.attach(E_LU, watch<&P::wake>(0, Wt_IDEM));
    z.attach(E_LU, watch<&P::wake>(1, Wt_IDEM));
  }
  void cleanup(void) {
    is_queued = false;
    x_change = z_change = false;
  }

  bool check_sat(ctx_t& ctx) {
    int low(std::max(z.lb(ctx), x.lb(ctx) / k));
    int high(std::min(z.ub(ctx), x.ub(ctx) / k));
    return low <= high;
  }
  bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }

  bool propagate(vec<clause_elt>& confl) {
    if(x_change) {
      UPDATE_LB(z, lb(x)/k, expl<&P::ex_z_lb>(0));
      UPDATE_UB(z, ub(x)/k, expl<&P::ex_z_ub>(0));
    }
    if(z_change) {
      UPDATE_LB(x, k * lb(z), expl<&P::ex_x_lb>(0));
      UPDATE_UB(x, k * ub(z) + k-1, expl<&P::ex_x_ub>(0));
    }
    return true;
  }

  intvar z;
  intvar x;
  int k;

  bool x_change;
  bool z_change;
};

class idiv_nonneg : public propagator, public prop_inst<idiv_nonneg> {
  // Queueing
  enum Status { S_Red = 2 };

  watch_result wake(int _xi) {
    if(status & S_Red)
      return Wt_Keep;

    queue_prop();
    return Wt_Keep;
  }

  // Explanations. Naive for now
  // z >= ceil[ lb(x)+1, ub(y) ] - 1
  void ex_z_lb(int _xi, pval_t p, vec<clause_elt>& expl) {
    int z_lb = z.lb_of_pval(p);
    int x_lb = (iceil(lb_prev(x)+1, ub(y)) - 1 >= z_lb) ? lb_prev(x) : lb(x);
    int y_ub = (iceil(x_lb+1, ub_prev(y)) - 1 >= z_lb) ? ub_prev(y) : ub(y);
    expl.push(x < x_lb);
    expl.push(y > y_ub);
  }

  // z <= ub(x)/lb(y); 
  void ex_z_ub(int _xi, pval_t pval, vec<clause_elt>& expl) {
    int z_ub = z.ub_of_pval(pval);
    
    int x_ub = (ub_prev(x) / lb(y) <= z_ub) ? ub_prev(x) : ub(x);
    int y_lb = (x_ub / lb_prev(y) <= z_ub) ? lb_prev(y) : lb(y);
    // Can probably weaken further
    expl.push(x > x_ub);
    expl.push(y < y_lb);
  }

  // x >= lb(z) * lb(y)
  void ex_x_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    int x_lb = x.lb_of_pval(p);

    int z_lb = (lb_prev(z) * lb(y) >= x_lb) ? lb_prev(z) : lb(z);
    int y_lb = (z_lb * lb_prev(y) >= x_lb) ? lb_prev(y) : lb(y);
    expl.push(z < z_lb);
    expl.push(y < y_lb);
  }
  // x <= (ub(z)+1) * ub(y) - 1;
  void ex_x_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    int x_ub = x.ub_of_pval(p) + 1;
    
    int z_ub = ((ub_prev(z)+1) * ub(y) <= x_ub) ? ub_prev(z) : ub(z);
    int y_ub = ((z_ub+1) * ub_prev(y) <= x_ub) ? ub_prev(y) : ub(y);
    expl.push(z > z_ub);
    expl.push(y > y_ub);
  }

  // y >= iceil(lb(x)+1, ub(z)+1);
  void ex_y_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    int y_lb = y.lb_of_pval(p);

    int x_lb = (iceil(lb_prev(x)+1, ub(z)+1) >= y_lb) ? lb_prev(x) : lb(x);
    int z_ub = (iceil(x_lb+1, ub_prev(z)+1) >= y_lb) ? ub_prev(z) : ub(z);
    expl.push(z > z_ub);
    expl.push(x < x_lb);
  }
  // y <= ub(x)/lb(z);
  void ex_y_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    int y_ub = y.ub_of_pval(p);

    int x_ub = (ub_prev(x)/lb(z) <= y_ub) ? ub_prev(x) : ub(x);
    int z_lb = (x_ub/lb_prev(z) <= y_ub) ? lb_prev(z) : lb(z);
    expl.push(z < z_lb);
    expl.push(x > x_ub);
  }

public:
  idiv_nonneg(solver_data* s, patom_t _r, intvar _z, intvar _x, intvar _y)
    : propagator(s), r(_r), z(_z), x(_x), y(_y), status(0) {
      assert(s->state.is_entailed_l0(r));
    z.attach(E_LU, watch_callback(wake_default, this, 2));
    x.attach(E_LU, watch_callback(wake_default, this, 0));
    y.attach(E_LU, watch_callback(wake_default, this, 1));
  }

  bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_PROP
    std::cerr << "[[Running idiv(+)]]" << std::endl;
#endif
    // What do the constraints look like?
    // (1) x >= z * y
    // (2) x < (z+1) * y
    // Propagate x
    int x_low = lb(z) * lb(y);
    int x_high = (ub(z)+1) * ub(y) - 1;
    if(x_low > lb(x) && !set_lb(x, x_low, ex_thunk(ex<&P::ex_x_lb>, 0, expl_thunk::Ex_BTPRED)))
      return false;
    if(x_high < ub(x) && !set_ub(x, x_high, ex_thunk(ex<&P::ex_x_ub>, 0, expl_thunk::Ex_BTPRED)))
      return false;

    // ... and y
    int y_low = iceil(lb(x)+1, ub(z)+1);
    int y_high = ub(x)/lb(z);
    if(y_low > lb(y) &&
      !set_lb(y, y_low, ex_thunk(ex<&P::ex_y_lb>, 0, expl_thunk::Ex_BTPRED)))
      return false;
    if(y_high < ub(y) &&
      !set_ub(y, y_low, ex_thunk(ex<&P::ex_y_ub>, 0, expl_thunk::Ex_BTPRED)))
      return false;

    // ... and z
    int z_low = iceil(lb(x)+1, ub(y)) - 1;
    int z_high = ub(x)/lb(y); 
    if(z_low > lb(z)
      && !set_lb(z, z_low, ex_thunk(ex<&P::ex_z_lb>, 0, expl_thunk::Ex_BTPRED)))
      return false;

    if(z_high > ub(z)
      && !set_ub(z, z_high, ex_thunk(ex<&P::ex_z_ub>, 0, expl_thunk::Ex_BTPRED)))
      return false;
    /*
    int z_low = lb(x) / ub(y);
    if(z_low > lb(z)) {
      if(!set_lb(z, z_low, ex_thunk(ex<&P::ex_z_lb>,0, expl_thunk::Ex_BTPRED)))
        return false;
    }
    int z_high = ub(x) / lb(y);
    if(z_high < ub(z)) {
      if(!set_ub(z, z_high, ex_thunk(ex<&P::ex_z_ub>,0, expl_thunk::Ex_BTPRED)))
        return false;
    }

    // Now x: smallest x s.t. x / lb(y) >= lb(z)
    int x_low = lb(z) * lb(y);
    if(x_low > lb(x)) {
      if(!set_lb(x, x_low, ex_thunk(ex<&P::ex_x_lb>, 0, expl_thunk::Ex_BTPRED)))
        return false;
    }
    // Greatest x s.t. x / ub(y) <= ub(z)
    int x_high = (ub(z)+1) * ub(y) - 1;
    if(x_high < ub(x)) {
      if(!set_ub(x, x_high, ex_thunk(ex<&P::ex_x_ub>, 0, expl_thunk::Ex_BTPRED)))
        return false;
    }

    // Same for y: smallest y s.t. lb(x) / y <= ub(z)
    int y_low = iceil(lb(x), ub(z));
    if(y_low > lb(y)) {
      if(!set_lb(y, y_low, ex_thunk(ex<&P::ex_y_lb>, 0, expl_thunk::Ex_BTPRED)))
        return false;
    }
    int y_high = iceil(ub(x), lb(z));
    if(y_high < ub(y)) {
      if(!set_ub(y, y_high, ex_thunk(ex<&P::ex_y_lb>, 0, expl_thunk::Ex_BTPRED)))
        return false;
    }
    */

    return true;
  }

  patom_t r;
  intvar z;
  intvar x;
  intvar y;

  char status;
};

bool post_idiv_nonneg(solver_data* s, intvar z, intvar x, intvar y) {
  // FIXME: Cheapo implementation appears to be wrong
#if 0
  intvar x_low(new_intvar(s, z.lb(s) * y.lb(s), z.ub(s) * y.ub(s)));
  intvar x_high(new_intvar(s, z.lb(s) * y.lb(s) - 1, (z.ub(s)+1) * y.ub(s) - 1));
  new iprod_nonneg(s, at_True, x_low, z, y);
  new iprod_nonneg(s, at_True, x_high+1, z+1, y);
  int_leq(s, x_low, x, 0);
  int_leq(s, x, x_high, 0);
  return true;
#else
  if(z.lb(s) < 0 && !enqueue(*s, z >= 0, reason()))
    return false;
  // new idiv_nonneg(s, at_True, z, x, y);
  return idiv_nonneg::post(s, at_True, z, x, y);
#endif
}

bool int_div(solver_data* s, intvar z, intvar x, intvar y, patom_t r) {
  assert(r == at_True);

  if(!enqueue(*s, y != 0, reason()))
    return false;
  
  if(y.is_fixed(s)) {
    // Constant
    int k = y.lb(s);
    if(y.lb(s) > 0)
      return idiv_xk::post(s, z, x, k);
    else
      return idiv_xk::post(s, -z, x, -k);
  }

  // Check the sign cases.
  // TODO: This doesn't handle the case when, say, z & x are fixed-sign.
  if(x.lb(s) >= 0) {
    if(y.lb(s) >= 0) {
      return post_idiv_nonneg(s, z, x, y);
    } else if(y.ub(s) <= 0) {
      return post_idiv_nonneg(s, -z, x, -y);
    }
  } else if(x.ub(s) <= 0) {
    if(y.lb(s) >= 0) {
      return post_idiv_nonneg(s, -z, -x, y);
    } else if(y.ub(s) <= 0) {
      return post_idiv_nonneg(s, z, -x, -y);
    }
  }
  // TODO: Implement non-sign-fixed case.
  GEAS_NOT_YET;
  return false;
}

}
