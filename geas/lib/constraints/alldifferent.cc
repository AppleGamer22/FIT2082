#ifndef PHAGE_ALLDIFFERENT_H
#define PHAGE_ALLDIFFERENT_H
#include <numeric>

#include <geas/mtl/bool-set.h>
#include <geas/utils/ordered-perm.h>
#include <geas/engine/propagator.h>
#include <geas/engine/propagator_ext.h>
#include <geas/vars/intvar.h>
#include <geas/utils/bitops.h>
#include <geas/utils/cast.h>

namespace geas {
  
class alldiff_v : public propagator, public prop_inst<alldiff_v> {
  watch_result wake(int xi) {
    fixed.push(xi);
    queue_prop();
    return Wt_Keep; 
  }
public:
  alldiff_v(solver_data* s, const vec<intvar>& _xs)
    : propagator(s), xs(_xs) {
    for(int ii : irange(xs.size())) {
      if(is_fixed(xs[ii])) {
        // Kill the value in other vars
        intvar::val_t k(lb(xs[ii]));
        for(int jj : irange(xs.size())) {
          if(ii == jj) continue;
          if(in_domain(xs[jj], k)) {
            if(!enqueue(*s, xs[jj] != k, reason()))
              throw RootFail();
          }
        }
      } else {
        xs[ii].attach(E_FIX, watch<&P::wake>(ii, Wt_IDEM));
      }
    }
  }

  bool propagate(vec<clause_elt>& confl) {
    for(int xi : fixed) {
      intvar::val_t k(lb(xs[xi]));
      patom_t r(xs[xi] != k);
      assert(s->state.is_inconsistent(r));

      for(int ii : irange(xi)) {
        if(in_domain(xs[ii], k)) {
          if(!enqueue(*s, xs[ii] != k, r))
            return false;
        }
      }
      for(int ii : irange(xi+1, xs.size())) {
        if(in_domain(xs[ii], k)) {
          if(!enqueue(*s, xs[ii] != k, r))
            return false;
        }
      }
    }
    fixed.clear();

    return true;
  }

  void cleanup(void) {
    fixed.clear();
    is_queued = false;
  }

  vec<intvar> xs;

  vec<int> fixed;
};

// If the link points down, there's slack.
// If it points up, it's a union-find.
struct tl_entry {
  int link;
  int cap;
};
/*
struct timeline {
  int find(int k) {
    if(tl[k].link > k)
      return tl[k].link = find(tl[k].link);
    return k;
  }
  
  int extend(int k) {
    k = find(k);
    tl[k].cap -= 1;
    if(tl[k].cap) {
      return k;
    } else {

    }
  }

  vec<tl_entry> tl;
};
*/

class alldiff_b : public propagator, public prop_inst<alldiff_b> {
  typedef typename intvar::val_t val_t;
  struct ex_info {
    int hall_lb;
    int hall_ub; // Open
    int var;
  };

  int mk_ex(int hall_lb, int hall_ub, int var) {
    int ei = exs.size();
    trail_save(s->persist, exs._size(), exs_saved);
    exs.push(ex_info { hall_lb, hall_ub, var }); 
    return ei;
  }
  // Explanations currently don't do any weakening;
  // picks the largest hall interval.
  void ex_lb(int ei, pval_t _p, vec<clause_elt>& expl) {
    ex_info& e(exs[ei]); 
    expl.push(xs[e.var] < e.hall_lb);
    int count = e.hall_ub - e.hall_lb;
    for(int ii : irange(xs.size())) {
      if(ii == e.var)
        continue;
      if(e.hall_lb <= lb(xs[ii]) && ub(xs[ii]) < e.hall_ub) {
        expl.push(xs[ii] < e.hall_lb);
        expl.push(xs[ii] >= e.hall_ub);
        --count;
        if(!count)
          return;
      }
    }
    GEAS_ERROR;
  }
  void ex_ub(int ei, pval_t _p, vec<clause_elt>& expl) {
    ex_info& e(exs[ei]); 
    expl.push(xs[e.var] >= e.hall_lb);
    int count = e.hall_ub - e.hall_lb;
    for(int ii : irange(xs.size())) {
      if(ii == e.var)
        continue;
      if(e.hall_lb <= lb(xs[ii]) && ub(xs[ii]) < e.hall_ub) {
        expl.push(xs[ii] < e.hall_lb);
        expl.push(xs[ii] >= e.hall_ub);
        --count;
        if(!count)
          return;
      }
    }
    GEAS_ERROR;
  }

  watch_result wake_lb(int xi) {
    queue_prop();
    // lb_low = std::min(lb_low, xs[xi].lb(s->wake_vals));
    return Wt_Keep;
  }
  watch_result wake_ub(int xi) {
    queue_prop();
    // ub_high = std::max(ub_high, xs[xi].ub(s->wake_vals));
    return Wt_Keep;
  }
  
  // Totally naive explanation: everything
  /*
  void ex_lb(int xi, pval_t p, vec<clause_elt>& expl) {
    for(int yi = 0; yi < xs.size(); ++yi) {
      expl.push(xs[yi] < lb(xs[yi]));
      expl.push(xs[yi] > ub(xs[yi]));
    }
  }

  void ex_ub(int xi, pval_t p, vec<clause_elt>& expl) {
    for(int yi = 0; yi < xs.size(); ++yi) {
      expl.push(xs[yi] < lb(xs[yi]));
      expl.push(xs[yi] > ub(xs[yi]));
    }
  }
  */


  public: 
    alldiff_b(solver_data* s, const vec<intvar>& _vs)
      : propagator(s), xs(_vs)
      , by_lb(s, xs.begin(), xs.end()), by_ub(s, xs.begin(), xs.end())
      , bounds(new int[2 * xs.size() + 2])
      , d(new int[2 * xs.size() + 2])
      , t(new int[2 * xs.size() + 2])
      , h(new int[2 * xs.size() + 2])
      , minrank(new int[xs.size()])
      , maxrank(new int[xs.size()])
      , exs_saved(false)
      // , lb_low(INT_MIN), ub_high(INT_MAX)
    {
      for(int ii : irange(xs.size())) {
        xs[ii].attach(E_LB, watch<&P::wake_lb>(ii));
        xs[ii].attach(E_UB, watch<&P::wake_ub>(ii));
      }
      queue_prop();
    }
    ~alldiff_b(void) {
      delete[] bounds;
      delete[] d;
      delete[] h;
      delete[] minrank;
      delete[] maxrank;
    }

    void root_simplify(void) {
      return; 
    }

    void cleanup(void) {
      is_queued = false;
      /*
      lb_low = INT_MAX;
      ub_high = INT_MIN;
      */
    }

    // Totally dumb satisfiability checker: for each pair of interesting end-points,
    // count the number of definitely within.
    bool check_sat(ctx_t& ctx) {
      // fprintf(stderr, "%% Checking alldiff_b.\n");
      vec<int> starts;
      vec<int> ends;
      for(intvar x : xs) {
        starts.push(x.lb(s));
        ends.push(x.ub(s)+1);
      }
      std::sort(starts.begin(), starts.end());
      std::sort(ends.begin(), ends.end());
      
      int* ss(starts.begin()); 
      int* se(starts.end());
      for(int en : ends) {
        // Find the range of starts left of e.
        while(ss != se && (*ss) < en)
          ++ss;
        int* sb(starts.begin());
        for(; sb != ss; ++sb) {
          int st(*sb);
          // Count the number of variables with within [st,en].
          int c(std::accumulate(xs.begin(), xs.end(), 0,
            [&ctx,st,en](int acc, const intvar& x) { return acc + ((st <= x.lb(ctx) && x.ub(ctx) < en) ? 1 : 0); }));
          // If so, fail.
          if(en - st < c)
            return false;
        }
      }
      return true;
    }
    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
    

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running alldiff]]" << std::endl;
#endif
      setup();
      
#if 0
      fprintf(stderr, "%% Alldiff bounds:");
      for(unsigned int xi : irange(xs.size())) {
        fprintf(stderr, " x%d: [%d, %d]", xi, (int) xs[xi].lb(s), (int) xs[xi].ub(s));        
      }
      fprintf(stderr, "\n");
#endif

      if(!update_lb(confl))
        return false;        
      if(!update_ub(confl))
        return false;
      /*
      for(int ii : irange(xs.size())) {
        lbs[ii] = lb(xs[ii]);
        ubs[ii] = ub(xs[ii]);
      }
      std::sort(lb_ord.begin(), lb_ord.end(), bound_cmp(lbs));
      std::sort(ub_ord.begin(), ub_ord.end(), bound_cmp(ubs));
      */

      return true;
    }

    static int pathmax(int* p, int k) {
      while(k < p[k])
        k = p[k];
      return k;
    }
    static int pathmin(int* p, int k) {
      while(k > p[k])
        k = p[k];
      return k;
    }
    static void pathset(int* a, int x, int y, int z) {
      int o = a[x];
      while(x != y) {
        a[x] = z;
        x = o;
        o = a[x];
      }
    }

    void setup(void) {
      const vec<unsigned int>& lb_ord(by_lb.get());
      const vec<unsigned int>& ub_ord(by_ub.get());
      
      int b(lb(xs[lb_ord[0]]));
      bounds[0] = b-xs.size();
      bounds[1] = b;
      nb = 1;
      unsigned int* u_it(ub_ord.begin());
      int u_b(ub(xs[*u_it])+1);
      // Process the 
      for(unsigned int ii : lb_ord) {
        int l_i(lb(xs[ii]));
        // Process any upper bounds which are _strictly_ below the next lb.
        while(u_b < l_i) {
          if(b < u_b) {
            ++nb;
            bounds[nb] = b = u_b;
          }
          maxrank[*u_it] = nb;
          ++u_it;
          u_b = ub(xs[*u_it])+1;
        }
        // And now do the lb.
        if(b < l_i) {
          ++nb;
          bounds[nb] = b = l_i;
        }
        minrank[ii] = nb;
      }
      // Now process the remaining upper bounds.
      for(; u_it != ub_ord.end(); ++u_it) {
        u_b = ub(xs[*u_it])+1;
        if(b < u_b) {
          ++nb;
          bounds[nb] = b = u_b;
        }
        maxrank[*u_it] = nb;
      }
      bounds[nb+1] = u_b+xs.size();
    }

    bool update_lb(vec<clause_elt>& confl) {
      // Assumes setup() has been called.

      // Initialize the timeline
      for(int i = 1; i <= nb+1; i++) {
        t[i] = h[i] = i-1;  
        d[i] = bounds[i] - bounds[i-1];
      }
      
      const vec<unsigned int>& ord(by_ub.get());
      for(unsigned int i : ord) {
        int x = minrank[i];
        int y = maxrank[i];
        int z = pathmax(t, x+1);
        int j = t[z];
        if(--d[z] == 0) {
          t[z] = z+1;
          z = pathmax(t, t[z]);
          t[z] = j;
        }
        pathset(t, x+1, z, z);
        if(d[z] < bounds[z] - bounds[y]) {
          // Set up conflict. We've been working by increasing ub, so 
          // bounds[y] is the right bound of a hall interval.
#if 0
          int hallmin = bounds[t[z]];
          int hallmax = bounds[y];
          int delta = 1 + hallmax - hallmin;
          assert(delta > 0);
          confl.clear();
          for(intvar x : xs) {
            if(hallmin <= x.lb(s) && x.ub(s) < hallmax) {
              confl.push(x < hallmin);
              confl.push(x >= hallmax);
              --delta;
              if(!delta)
                return false;
            }
          }
          GEAS_ERROR;
#else
          // Process by _decreasing_ lower bound, to collect
          // the smallest suitable hall set.
          int hallmax = bounds[y]; 
          const vec<unsigned int>& hord(by_lb.get());
          unsigned int count = 0;
          vec<unsigned int> mem;
          for(int ii = hord.size()-1; ii >= 0; --ii) {
            int xi(hord[ii]);
            if(hallmax <= ub(xs[xi]))
              continue;
            mem.push(xi);
            ++count;
            if(hallmax - lb(xs[xi]) < count) {
              // Found our hall set.
              int hallmin = lb(xs[xi]);
              for(int yi : mem) {
                confl.push(xs[yi] < hallmin);
                confl.push(xs[yi] >= hallmax);
              }
              return false;
            }
          }
          GEAS_ERROR;
#endif
        }
        if(h[x] > x) {
          int w = pathmax(h, h[x]);
          // maxsorted[i]->min = bounds[w];
          // if(!set_lb(xs[i], bounds[w], expl<&P::ex_lb>(i, expl_thunk::Ex_BTPRED)))
          if(!set_lb(xs[i], bounds[w], expl<&P::ex_lb>(mk_ex(bounds[t[z]], bounds[y], i), expl_thunk::Ex_BTPRED)))
            return false;
          pathset(h, x, w, w);
          h[y] = j-1;
        }
      }
      return true;
    }

    bool update_ub(vec<clause_elt>& confl) {
      // Assumes setup() has been called.

      // Initialize the timeline
      for(int i = 0; i <= nb; i++) {
        t[i] = h[i] = i+1;  
        d[i] = bounds[i+1] - bounds[i];
      }
      
      // Process by _decreasing_ lb.
      const vec<unsigned int>& ord(by_lb.get());
      for(int p = ord.size()-1; p >= 0; --p) {
        unsigned int i = ord[p];

        int x = minrank[i];
        int y = maxrank[i];
        int z = pathmin(t, y-1);
        int j = t[z];
        if(--d[z] == 0) {
          t[z] = z-1;
          z = pathmin(t, t[z]);
          t[z] = j;
        }
        pathset(t, y-1, z, z);
        if(d[z] < bounds[x] - bounds[z]) {
          // Set up conflict. Because we're processing by
          // decreasing lb, bounds[x] is the left bound of the hall interval.
          int hallmin = bounds[x];
#if 0
          int hallmax = bounds[t[z]];
          int delta = 1 + hallmax - hallmin;
          assert(delta > 0);
          confl.clear();
          for(intvar x : xs) {
            if(hallmin <= x.lb(s) && x.ub(s) < hallmax) {
              confl.push(x < hallmin);
              confl.push(x >= hallmax);
              --delta;
              if(!delta)
                return false;
            }
          }
#else
          // Process bounds by increasing ub, to collet the smallest over-full interval.
          unsigned int count = 0;
          vec<unsigned int> mem;
          for(int xi : by_ub.get()) {
            if(lb(xs[xi]) < hallmin)
              continue;
            count++;
            mem.push(xi);
            if(ub(xs[xi]) - hallmin + 1 < count) {
              // Found an interval
              int hallmax = ub(xs[xi]);
              for(int yi : mem) {
                confl.push(xs[yi] < hallmin);
                confl.push(xs[yi] > hallmax);
              }
              return false;
            }
          }
#endif
          GEAS_ERROR;
        }
        if(h[y] < y) {
          int w = pathmin(h, h[y]);
          // maxsorted[i]->min = bounds[w];
          if(!set_ub(xs[i], bounds[w]-1, expl<&P::ex_ub>(mk_ex(bounds[x], bounds[t[z]], i), expl_thunk::Ex_BTPRED)))
            return false;
          pathset(h, x, w, w);
          h[x] = j+1;
        }
      }
      return true;
    }

    // Parameters
    vec<intvar> xs;

    // Persistent state
    OrderedPerm< By_LB<intvar> > by_lb;
    OrderedPerm< By_UB<intvar> > by_ub;
    // Transient state
    int nb;
    int* bounds; // Has capacity 2 * |Vars| + 2
    int* d; // Critical capacity deltas
    int* t; // Critical capacity pointers
    int* h; // Hall interval pointers
    // Capacity |Vars|
    int* minrank;
    int* maxrank;
    // We're only interested in landmarks 
    /*
    int lb_low;
    int ub_high;
    */
    // Cached explanation information
    vec<ex_info> exs;
    char exs_saved;
};


// Exactly the same as alldifferent, except we add a bunch of slack
// at the zero vertex.
class alldiff_ex0_b : public propagator, public prop_inst<alldiff_ex0_b> {
  typedef typename intvar::val_t val_t;
  struct ex_info {
    int hall_lb;
    int hall_ub; // Open
    int var;
  };

  int mk_ex(int hall_lb, int hall_ub, int var) {
    int ei = exs.size();
    trail_save(s->persist, exs._size(), exs_saved);
    exs.push(ex_info { hall_lb, hall_ub, var }); 
    return ei;
  }
  // Explanations currently don't do any weakening;
  // picks the largest hall interval.
  void ex_lb(int ei, pval_t _p, vec<clause_elt>& expl) {
    ex_info& e(exs[ei]); 
    expl.push(xs[e.var] < e.hall_lb);
    int count = e.hall_ub - e.hall_lb;
    for(int ii : irange(xs.size())) {
      if(ii == e.var)
        continue;
      if(e.hall_lb <= lb(xs[ii]) && ub(xs[ii]) < e.hall_ub) {
        expl.push(xs[ii] < e.hall_lb);
        expl.push(xs[ii] >= e.hall_ub);
        --count;
        if(!count)
          return;
      }
    }
    GEAS_ERROR;
  }
  void ex_ub(int ei, pval_t _p, vec<clause_elt>& expl) {
    ex_info& e(exs[ei]); 
    expl.push(xs[e.var] >= e.hall_lb);
    int count = e.hall_ub - e.hall_lb;
    for(int ii : irange(xs.size())) {
      if(ii == e.var)
        continue;
      if(e.hall_lb <= lb(xs[ii]) && ub(xs[ii]) < e.hall_ub) {
        expl.push(xs[ii] < e.hall_lb);
        expl.push(xs[ii] >= e.hall_ub);
        --count;
        if(!count)
          return;
      }
    }
    GEAS_ERROR;
  }

  watch_result wake_lb(int xi) {
    queue_prop();
    // lb_low = std::min(lb_low, xs[xi].lb(s->wake_vals));
    return Wt_Keep;
  }
  watch_result wake_ub(int xi) {
    queue_prop();
    // ub_high = std::max(ub_high, xs[xi].ub(s->wake_vals));
    return Wt_Keep;
  }
  
  public: 
    alldiff_ex0_b(solver_data* s, const vec<intvar>& _vs)
      : propagator(s), xs(_vs)
      , by_lb(s, xs.begin(), xs.end()), by_ub(s, xs.begin(), xs.end())
      , bounds(new int[2 * xs.size() + 4])
      , d(new int[2 * xs.size() + 4])
      , t(new int[2 * xs.size() + 4])
      , h(new int[2 * xs.size() + 4])
      , minrank(new int[xs.size()+1])
      , maxrank(new int[xs.size()+1])
      , exs_saved(false)
      // , lb_low(INT_MIN), ub_high(INT_MAX)
    {
      for(int ii : irange(xs.size())) {
        xs[ii].attach(E_LB, watch<&P::wake_lb>(ii));
        xs[ii].attach(E_UB, watch<&P::wake_ub>(ii));
      }
      // Add the additional space
      intvar zero(new_intvar(s, 0, 0));
      xs.push(zero);
      by_lb.add(zero);
      by_ub.add(zero);

      queue_prop();
    }
    ~alldiff_ex0_b(void) {
      delete[] bounds;
      delete[] d;
      delete[] h;
      delete[] minrank;
      delete[] maxrank;
    }

    void root_simplify(void) {
      return; 
    }

    void cleanup(void) {
      is_queued = false;
      /*
      lb_low = INT_MAX;
      ub_high = INT_MIN;
      */
    }

    // Totally dumb satisfiability checker: for each pair of interesting end-points,
    // count the number of definitely within.
#if 0
    bool check_sat(ctx_t& ctx) {
      // fprintf(stderr, "%% Checking alldiff_ex0_b.\n");
      vec<int> starts;
      vec<int> ends;
      for(intvar x : xs) {
        starts.push(x.lb(s));
        ends.push(x.ub(s)+1);
      }
      std::sort(starts.begin(), starts.end());
      std::sort(ends.begin(), ends.end());
      
      int* ss(starts.begin()); 
      int* se(starts.end());
      for(int en : ends) {
        // Skip hall intervals over zero.
        if(ss <= 0 && 0 <= se)
          continue;
        // Find the range of starts left of e.
        while(ss != se && (*ss) < en)
          ++ss;
        int* sb(starts.begin());
        for(; sb != ss; ++sb) {
          int st(*sb);
          // Count the number of variables with within [st,en].
          int c(std::accumulate(xs.begin(), xs.end(), 0,
            [&ctx,st,en](int acc, const intvar& x) { return acc + ((st <= x.lb(ctx) && x.ub(ctx) < en) ? 1 : 0); }));
          // If so, fail.
          if(en - st < c)
            return false;
        }
      }
      return true;
    }
    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
#endif

    

    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running alldiff]]" << std::endl;
#endif
      setup();
      
#if 0
      fprintf(stderr, "%% Alldiff bounds:");
      for(unsigned int xi : irange(xs.size())) {
        fprintf(stderr, " x%d: [%d, %d]", xi, (int) xs[xi].lb(s), (int) xs[xi].ub(s));        
      }
      fprintf(stderr, "\n");
#endif

      if(!update_lb(confl))
        return false;        
      if(!update_ub(confl))
        return false;
      /*
      for(int ii : irange(xs.size())) {
        lbs[ii] = lb(xs[ii]);
        ubs[ii] = ub(xs[ii]);
      }
      std::sort(lb_ord.begin(), lb_ord.end(), bound_cmp(lbs));
      std::sort(ub_ord.begin(), ub_ord.end(), bound_cmp(ubs));
      */

      return true;
    }

    static int pathmax(int* p, int k) {
      while(k < p[k])
        k = p[k];
      return k;
    }
    static int pathmin(int* p, int k) {
      while(k > p[k])
        k = p[k];
      return k;
    }
    static void pathset(int* a, int x, int y, int z) {
      int o = a[x];
      while(x != y) {
        a[x] = z;
        x = o;
        o = a[x];
      }
    }

    void setup(void) {
      const vec<unsigned int>& lb_ord(by_lb.get());
      const vec<unsigned int>& ub_ord(by_ub.get());
      
      int b(lb(xs[lb_ord[0]]));
      bounds[0] = b-xs.size();
      bounds[1] = b;
      nb = 1;
      unsigned int* u_it(ub_ord.begin());
      int u_b(ub(xs[*u_it])+1);
      // Process the 
      for(unsigned int ii : lb_ord) {
        int l_i(lb(xs[ii]));
        // Process any upper bounds which are _strictly_ below the next lb.
        while(u_b < l_i) {
          if(b < u_b) {
            ++nb;
            bounds[nb] = b = u_b;
          }
          maxrank[*u_it] = nb;
          ++u_it;
          u_b = ub(xs[*u_it])+1;
        }
        // And now do the lb.
        if(b < l_i) {
          ++nb;
          bounds[nb] = b = l_i;
        }
        minrank[ii] = nb;
      }
      // Now process the remaining upper bounds.
      for(; u_it != ub_ord.end(); ++u_it) {
        u_b = ub(xs[*u_it])+1;
        if(b < u_b) {
          ++nb;
          bounds[nb] = b = u_b;
        }
        maxrank[*u_it] = nb;
      }
      bounds[nb+1] = u_b+xs.size();
    }

    bool update_lb(vec<clause_elt>& confl) {
      // Assumes setup() has been called.

      // Initialize the timeline
      for(int i = 1; i <= nb+1; i++) {
        t[i] = h[i] = i-1;  
        d[i] = bounds[i] - bounds[i-1];
      }
      // Correct the delta for zero
      d[maxrank[xs.size()-1]] = xs.size();
      
      const vec<unsigned int>& ord(by_ub.get());
      for(unsigned int i : ord) {
        // Skip the dummy placeholder.
        if(i == xs.size())
          continue;
        int x = minrank[i];
        int y = maxrank[i];
        int z = pathmax(t, x+1);
        int j = t[z];
        if(--d[z] == 0) {
          t[z] = z+1;
          z = pathmax(t, t[z]);
          t[z] = j;
        }
        pathset(t, x+1, z, z);
        if(d[z] < bounds[z] - bounds[y]) {
          // Set up conflict. We've been working by increasing ub, so 
          // bounds[y] is the right bound of a hall interval.
#if 0
          int hallmin = bounds[t[z]];
          int hallmax = bounds[y];
          int delta = 1 + hallmax - hallmin;
          assert(delta > 0);
          confl.clear();
          for(intvar x : xs) {
            if(hallmin <= x.lb(s) && x.ub(s) < hallmax) {
              confl.push(x < hallmin);
              confl.push(x >= hallmax);
              --delta;
              if(!delta)
                return false;
            }
          }
          GEAS_ERROR;
#else
          // Process by _decreasing_ lower bound, to collect
          // the smallest suitable hall set.
          int hallmax = bounds[y]; 
          const vec<unsigned int>& hord(by_lb.get());
          unsigned int count = 0;
          vec<unsigned int> mem;
          for(int ii = hord.size()-1; ii >= 0; --ii) {
            int xi(hord[ii]);
            if(hallmax <= ub(xs[xi]))
              continue;
            mem.push(xi);
            ++count;
            if(hallmax - lb(xs[xi]) < count) {
              // Found our hall set.
              int hallmin = lb(xs[xi]);
              for(int yi : mem) {
                confl.push(xs[yi] < hallmin);
                confl.push(xs[yi] >= hallmax);
              }
              return false;
            }
          }
          GEAS_ERROR;
#endif
        }
        if(h[x] > x) {
          int w = pathmax(h, h[x]);
          // maxsorted[i]->min = bounds[w];
          // if(!set_lb(xs[i], bounds[w], expl<&P::ex_lb>(i, expl_thunk::Ex_BTPRED)))
          if(!set_lb(xs[i], bounds[w], expl<&P::ex_lb>(mk_ex(bounds[t[z]], bounds[y], i), expl_thunk::Ex_BTPRED)))
            return false;
          pathset(h, x, w, w);
          h[y] = j-1;
        }
      }
      return true;
    }

    bool update_ub(vec<clause_elt>& confl) {
      // Assumes setup() has been called.

      // Initialize the timeline
      for(int i = 0; i <= nb; i++) {
        t[i] = h[i] = i+1;  
        d[i] = bounds[i+1] - bounds[i];
      }
      d[minrank[xs.size()-1]] = xs.size();
      
      // Process by _decreasing_ lb.
      const vec<unsigned int>& ord(by_lb.get());
      for(int p = ord.size()-1; p >= 0; --p) {
        unsigned int i = ord[p];
        if(i == xs.size())
          continue;

        int x = minrank[i];
        int y = maxrank[i];
        int z = pathmin(t, y-1);
        int j = t[z];
        if(--d[z] == 0) {
          t[z] = z-1;
          z = pathmin(t, t[z]);
          t[z] = j;
        }
        pathset(t, y-1, z, z);
        if(d[z] < bounds[x] - bounds[z]) {
          // Set up conflict. Because we're processing by
          // decreasing lb, bounds[x] is the left bound of the hall interval.
          int hallmin = bounds[x];
#if 0
          int hallmax = bounds[t[z]];
          int delta = 1 + hallmax - hallmin;
          assert(delta > 0);
          confl.clear();
          for(intvar x : xs) {
            if(hallmin <= x.lb(s) && x.ub(s) < hallmax) {
              confl.push(x < hallmin);
              confl.push(x >= hallmax);
              --delta;
              if(!delta)
                return false;
            }
          }
#else
          // Process bounds by increasing ub, to collet the smallest over-full interval.
          unsigned int count = 0;
          vec<unsigned int> mem;
          for(int xi : by_ub.get()) {
            if(lb(xs[xi]) < hallmin)
              continue;
            count++;
            mem.push(xi);
            if(ub(xs[xi]) - hallmin + 1 < count) {
              // Found an interval
              int hallmax = ub(xs[xi]);
              for(int yi : mem) {
                confl.push(xs[yi] < hallmin);
                confl.push(xs[yi] > hallmax);
              }
              return false;
            }
          }
#endif
          GEAS_ERROR;
        }
        if(h[y] < y) {
          int w = pathmin(h, h[y]);
          // maxsorted[i]->min = bounds[w];
          if(!set_ub(xs[i], bounds[w]-1, expl<&P::ex_ub>(mk_ex(bounds[x], bounds[t[z]], i), expl_thunk::Ex_BTPRED)))
            return false;
          pathset(h, x, w, w);
          h[x] = j+1;
        }
      }
      return true;
    }

    // Parameters
    vec<intvar> xs;

    // Persistent state
    OrderedPerm< By_LB<intvar> > by_lb;
    OrderedPerm< By_UB<intvar> > by_ub;
    // Transient state
    int nb;
    int* bounds; // Has capacity 2 * |Vars| + 2
    int* d; // Critical capacity deltas
    int* t; // Critical capacity pointers
    int* h; // Hall interval pointers
    // Capacity |Vars|
    int* minrank;
    int* maxrank;
    // We're only interested in landmarks 
    /*
    int lb_low;
    int ub_high;
    */
    // Cached explanation information
    vec<ex_info> exs;
    char exs_saved;
};

using namespace B64;
class alldiff_dc : public propagator, public prop_inst<alldiff_dc> {
  typedef typename intvar::val_t val_t;

  // FILL ME
  struct ex_info {
    ex_info(void) : scc_begin(0), scc_end(0) { }
    ex_info(int _scc_begin, int _scc_end)
      : scc_begin(_scc_begin), scc_end(_scc_end) { }
    int scc_begin : 16;
    int scc_end : 16;
  };
  
  struct queue_entry {
    unsigned base;
    uint64_t bits;
  };

  inline void rem_(uint64_t* dom, char* saved, int val) {
    trail_save(s->persist, dom[block(val)], saved[block(val)]);
    dom[block(val)] &= ~bit(val);
  }

  inline void rem_dom(int var, int val) {
    rem_(dom[var], dom_saved[var], val);
    rem_(inv_dom[val], inv_dom_saved[val], var);
  }

  void ex_rem(int ei, pval_t _p, vec<clause_elt>& expl) {
    ex_info ex(cast::conv<ex_info>(ei));
    
    // Collect the values in the Hall set.
    #if 1
    for(int ii = ex.scc_begin; ii < ex.scc_end; ++ii) {
      int v(match[sccs[ii]]);
      seen[block(v)] |= bit(v);
    }
    // Variables in the SCC must take some outside value.
    for(int ii = ex.scc_begin; ii < ex.scc_end; ++ii) {
      int xi(sccs[ii]);
      uint64_t* x_dom0(dom0[xi]);
      for(int b = 0; b < req_words(dom_sz); ++b) {
        uint64_t word(x_dom0[b] & ~seen[b]);
        // Iter_Word(low + (b << block_bits()), word, [this, &expl, xi](int c) {
        //     EX_PUSH(expl, xs[xi] == c);
        //   });
        Iter_Word((b << block_bits()), word, [this, &expl, xi](int c) {
            EX_PUSH(expl, eq_atoms[xi][c]);
          });
      }
    }
    clear_seen();
    #else
    int ex_lb = dom_sz;
    int ex_ub = -1;
    for(int ii = ex.scc_begin; ii < ex.scc_end; ++ii) {
      int v(match[sccs[ii]]);
      seen[block(v)] |= bit(v);
      ex_lb = std::min(ex_lb, v);
      ex_ub = std::max(ex_ub, v);
    }
    // Could do bit-vector stuff here.
    repair_tl = repair_queue;
    for(int ii = ex_lb+1; ii < ex_ub-1; ++ii) {
      if(! (seen[block(ii)] & bit(ii)) ) {
        *repair_tl = ii;
        ++repair_tl;
      }
    }
    clear_seen();
    // Variables in the SCC must take some outside value.
    if(0 < ex_lb) {
      for(int xi : range(&sccs[ex.scc_begin], &sccs[ex.scc_end]))
        EX_PUSH(expl, xs[xi] < low + ex_lb);
    }
    if(ex_ub < dom_sz) {
      for(int xi : range(&sccs[ex.scc_begin], &sccs[ex.scc_end]))
        EX_PUSH(expl, xs[xi] > low + ex_ub);
    }
    for(int ii = ex.scc_begin; ii < ex.scc_end; ++ii) {
      int xi(sccs[ii]);
      uint64_t* x_dom0(dom0[xi]);
      for(int c : range(repair_queue, repair_tl)) {
        if(x_dom0[block(c)] & bit(c)) {
          EX_PUSH(expl, eq_atoms[xi][c]);
        }
      }
    }
    repair_tl = repair_queue;
    #endif
  }

  struct attachment {
    attachment(void) : var(0), val(0) { }
    attachment(int _var, int _val)
      : var(_var), val(_val) {
      assert(_var < 1 << 16);
      assert(_val < 1 << 16);
    }
    int var : 16;
    int val : 16;
  };
  watch_result wake_val(int att) {
    attachment c = cast::conv<attachment>(att);
    // Update the forward and inverse domains.
    rem_dom(c.var, c.val);
    // Check if we need to repair the matching.
    if(match[c.var] == c.val) {
      *repair_tl = c.val;
      ++repair_tl;
    }
    // Make sure we process the SCC containing c.var.
    touched[block(c.var)] |= bit(c.var);
    
    queue_prop();
    return Wt_Keep;
  }
  inline static int compute_dom_min(solver_data* s, const vec<intvar>& xs) {
    auto it(xs.begin()); ++it;
    return std::accumulate(it, xs.end(), xs[0].lb(s),
                           [s](int low, const intvar& x) { return std::min(low, (int) x.lb(s)); });
  }
  inline static int compute_dom_max(solver_data* s, const vec<intvar>& xs) {
    auto it(xs.begin()); ++it;
    return std::accumulate(it, xs.end(), xs[0].ub(s),
                           [s](int high, const intvar& x) { return std::max(high, (int) x.ub(s)); });
  }

  public: 
            
    alldiff_dc(solver_data* s, const vec<intvar>& _vs)
      : propagator(s, PRIO_LOW), xs(_vs)
      , sz(_vs.size())
      , dom_sz(1 + compute_dom_max(s, _vs) - compute_dom_min(s, _vs))
      , low(compute_dom_min(s, _vs))
        // Persistent state
      , match(new int[sz])
      , inv_match(new int[dom_sz])
      , unmatched(new uint64_t[req_words(dom_sz)])

        // Helper structures
      , rseen(new uint64_t[req_words(sz)])
      , seen(new uint64_t[req_words(dom_sz)])
      , pred(new int[dom_sz])
      // , lb_low(INT_MIN), ub_high(INT_MAX)

      , match_queue(new int[dom_sz])
      , repair_queue(new int[dom_sz])
      , repair_tl(repair_queue)
      , touched(new uint64_t[req_words(sz)])

        // SCC stuff
      , dfs_num(new int[sz])
      , lowlink(new int[sz])
      , dfs_count(0)
      , stack(new int[sz])
      , stack_tl(stack)
      , on_stack(new bool[sz])

      , sccs(new int[sz])
      , scc_idx(new int[sz])
      , scc_root(new int[sz])

      , exs_saved(false)
    {
      // Set up the scc mappings.
      scc_root[0] = sz;
      for(int ii : irange(1, sz))
        scc_root[ii] = 0;
      for(int ii : irange(sz)) {
        sccs[ii] = ii;
        scc_idx[ii] = ii;
      }
      memset(touched, 0, sizeof(uint64_t) * req_words(sz));
      memset(rseen, 0, sizeof(uint64_t) * req_words(sz));
      memset(seen, 0, sizeof(uint64_t) * req_words(dom_sz));
      memset(pred, 0, sizeof(int) * dom_sz);

      int high(compute_dom_max(s, xs));

      int v_idx = 0;
      for(int k = low; k <= high; ++k, ++v_idx) {
        uint64_t* k_inv(new uint64_t[req_words(sz)]);
        char* k_saved(new char[req_words(sz)]);
        memset(k_inv, 0, sizeof(uint64_t) * req_words(sz));
        memset(k_saved, 0, sizeof(char) * req_words(sz));
        inv_dom.push(k_inv);
        inv_dom_saved.push(k_saved);
      }

      int xi = 0;
      for(intvar x : xs) {
        // Initialize domains
        make_eager(x);
        uint64_t* x_dom(new uint64_t[req_words(dom_sz)]);
        uint64_t* x_dom0(new uint64_t[req_words(dom_sz)]);
        char* x_saved(new char[req_words(dom_sz)]);
        memset(x_dom, 0, sizeof(uint64_t) * req_words(dom_sz));
        memset(x_dom0, 0, sizeof(uint64_t) * req_words(dom_sz));
        memset(x_saved, 0, sizeof(char) * req_words(dom_sz));

        for(int c : x.domain(s->ctx())) {
          if(x.in_domain(s->ctx(), c)) {
            int k(c - low);
            x_dom[block(k)] |= bit(k);
            x_dom0[block(k)] |= bit(k);
            inv_dom[k][block(xi)] |= bit(xi);
            attach(s, x != c, watch<&P::wake_val>(cast::conv<int>(attachment(xi, k)), Wt_IDEM));
          }
        }
        eq_atoms.push();
        vec<patom_t>& x_eq(eq_atoms.last());
        for(int c = low; c < low + dom_sz; ++c)
          x_eq.push(x == c);

        dom.push(x_dom);
        dom0.push(x_dom0);
        dom_saved.push(x_saved);
        ++xi;
      }

      if(!init_match())
        throw RootFail { };
      // queue_prop();
    }

    ~alldiff_dc(void) {
      for(uint64_t* d : dom)
        delete[] d;
      for(char* s : dom_saved)
        delete[] s;

      delete[] rseen;
      delete[] seen;
      delete[] pred;

      delete[] match;
      delete[] inv_match;
      delete[] unmatched;

      delete[] match_queue;
      delete[] repair_queue;
      delete[] touched;

      delete[] sccs;
      delete[] scc_idx;
      delete[] scc_root;
      
      delete[] dfs_num;
      delete[] lowlink;
      delete[] stack;
      delete[] on_stack;
    }

    void root_simplify(void) {
      return; 
    }

    void cleanup(void) {
      is_queued = false;
      repair_tl = repair_queue;

      memset(touched, 0, sizeof(uint64_t) * req_words(sz));
    }

  #if 0
    // Totally dumb satisfiability checker: for each pair of interesting end-points,
    // count the number of definitely within.
    bool check_sat(ctx_t& ctx) {
      // fprintf(stderr, "%% Checking alldiff_b.\n");
      return true;
    }
    bool check_unsat(ctx_t& ctx) { return !check_sat(ctx); }
  #endif

  void log_state(void) {
    fprintf(stderr, "%%%% matching(%d): [x0 -> %d", prop_id, low + match[0]);
    for(int ii : irange(1, sz)) 
      fprintf(stderr, ", x%d -> %d", ii, low + match[ii]);
    fprintf(stderr, "];\n");
  }
    bool propagate(vec<clause_elt>& confl) {
#ifdef LOG_ALL
      std::cout << "[[Running alldiff(dc)]]" << std::endl;
#endif
      if(!repair_matching(confl))
        return false;

      // log_state();
      // return true;

      if(!trim_sccs())
        return false;

      return true;
    }

  inline void clear_seen(void) {
    memset(seen, 0, sizeof(uint64_t) * req_words(dom_sz));
  }

  bool init_match(void) {
    Fill_BV(unmatched, dom_sz);
    for(int ii : irange(sz)) {
      if(!extend_match(ii))
        return false;
      clear_seen();
    }
    return true;
  }

  inline bool repair_match(int val) {
    unmatched[block(val)] |= bit(val);
    if(!extend_match(inv_match[val])) {
      unmatched[block(val)] &= ~bit(val);
      return false;
    }
    return true;
  }

  // Remember to zero-out seen.
  bool extend_match(int target) {
    // Doing a breadth-first search
    // Make val (temporarily) unmatched.
    int* queue_hd = queue_tl = match_queue;
    // int* queue_ed = queue_hd;
    (*queue_tl) = target; ++queue_tl;

    for(; queue_hd < queue_tl; ++queue_hd) {
      int var(*queue_hd);
      uint64_t* var_dom(dom[var]);
      int bidx = 0;
      for(uint64_t word : range(dom[var], dom[var] + req_words(dom_sz))) {
        if(word & unmatched[bidx]) {
          // Found a matching, so reconstruct.
          int rval = (bidx << block_bits()) + __builtin_ctzll(word & unmatched[bidx]);

          unmatched[block(rval)] &= ~bit(rval);
          while(var != target) {
            int next_r = match[var];
            match[var] = rval;
            inv_match[rval] = var;
            rval = next_r;
            var = pred[rval];
          }
          match[target] = rval;
          inv_match[rval] = target;

          // Zero out the seen array.
          // memset(seen, 0, sizeof(uint64_t) * req_words(dom_sz));
          return true;
        } else if(word & ~seen[bidx]) {
          uint64_t mask(word & ~seen[bidx]);
          seen[bidx] |= word;
          Iter_Word(bidx << block_bits(), mask, [this, var](int val) {
              // Do something so we can reconstruct the matching.
              pred[val] = var;
              *queue_tl = inv_match[val];
              ++queue_tl;
            });
        }
        bidx++;
      }
    }
    return false;
  }

  bool repair_matching(vec<clause_elt>& confl) {
    int* repair_hd(repair_queue);
    for(; repair_hd < repair_tl; ++repair_hd) {
      if(!repair_match(*repair_hd)) {
        // Build explanation. Relies on queue_tl and seen being preserved.
        for(int xi : range(match_queue, queue_tl)) {
          uint64_t* x_dom0(dom0[xi]);
          for(unsigned b = 0; b < req_words(dom_sz); ++b) {
            uint64_t to_ex(x_dom0[b] & ~seen[b]);
            Iter_Word(low + (b << block_bits()), to_ex, [this,xi,&confl](int c) {
                EX_PUSH(confl, xs[xi] == c);
                  });
          }
        }
        clear_seen();
        return false;
      }
      clear_seen();
    }
    return true;
  }

  // Breadth-first SCC construction.
  /*
    // TODO: Finish implementing
  void process_scc(uint64_t* curr_scc) {
    // Pick a root. (Should really be random.)
    int r = Min_BV(curr_scc);

    // Compute the forward-reachable set (intersected with curr_scc)
    seen[block(match[r])] = bit(match[r]);
    int* match_hd = match_queue;
    int* match_tl = match_queue;
    (*match_tl) = r; ++match_tl;
    for(; match_hd < match_tl; ++match_hd) {
      int var = *match_hd;
      uint64_t* vdom(dom[var]);
      for(int b : irange(req_words(dom_sz))) {
        uint64_t word(vdom[b] & curr_scc[b] & ~seen[b]);
        if(word) {
          // Seen some new values, so enqueue the dual matches.
          seen[b] |= word;
          Iter_Word(b << block_bits(), word, [this, &match_tl](int c) {
              *match_tl = inv_match[c];
              ++match_tl;
            });
        }
      }
    }

    // Compute the reverse-reachable set (intersected etc.)
    match_hd = match_tl = match_queue;
    rseen[block(r)] |= bit(r);
    (*match_tl) = match[r]; ++match_tl;
    for(; match_hd < match_tl; ++match_hd) {
      int val = *match_hd;
      uint64_t* v_inv(inv_dom[val]);
      for(int b : irange(req_words(sz))) {
        uint64_t word(v_inv[b] & v_scc[b] & ~rseen[b]);
        if(word) {
          rseen[b] |= word;
          Iter_Word(b << block_bits(), word, [this, &match_tl](int c) {
              *match_tl = match[c];
              ++match_tl;
            });
        }
      }
    }

    // At this point, seen contains all the forward reachable values,
    // and rseen contains all the reverse-reachable vars.

    // Split the three cases.
    // Anything in both is in the current scc.

    // Now push the forward-reachable and rev-reachable as sub-SCCs.
  }
  */
  inline int find_scc_begin(int x) {
    int idx(scc_idx[x]);
    if(scc_root[idx] >= idx)
      return idx;
    int r = scc_root[idx];
    while(scc_root[r] <= idx)
      r = scc_root[r];
    //if(r != scc_root[idx])
    //  trail_change(s->persist, scc_root[idx], r);
    return r;
  }
  bool strongconnect(int x);
  bool strongconnect(int x, int& begin);
  bool trim_unmatched(int& begin, int end);

  bool trim_sccs(void) {
    // FIXME: Avoid initialization.
    for(int ii : irange(sz)) 
      dfs_num[ii] = 0;

    // Iterate over the touched variables
    int base(0);
    for(int b = 0; b < req_words(sz); ++b) {
      uint64_t word(touched[b]);
      while(word) {
        uint64_t tvar(base + __builtin_ctzll(word));
        word &= (word-1);
        if(!dfs_num[tvar]) {
          // Now find the SCC containing 
          int scc_begin(find_scc_begin(tvar));
          int scc_end(scc_root[scc_begin]);
          if(!trim_scc(scc_begin, scc_end)) {
            for(int x : range(stack, stack_tl))
              on_stack[x] = false;
            stack_tl = stack;
            return false;
          }
        }
      }
      base += 64;
    }
    return true;
  }
  // For now, just use standard Tarjan stuff.
  bool trim_scc(int scc_begin, int scc_end) {
    // First, mark any reachable unmatched values.
    if(!trim_unmatched(scc_begin, scc_end))
      return true;


    while(scc_begin < scc_end) {
      // No vertex should have been touched.
      assert(!dfs_num[sccs[scc_begin]]);
      // Strongconnnect should update scc_begin.
      if(!strongconnect(sccs[scc_begin], scc_begin))
        return false;
    }
    return true;
  }

    // Parameters
    vec<intvar> xs;
  int sz;
  int dom_sz;
  int low; // Offset for values.

  vec< vec<patom_t> > eq_atoms;
  
    // Persistent state. Caching domain values, for quick iteration.
  vec<uint64_t*> dom;
  vec<char*> dom_saved;
  vec<uint64_t*> dom0;

  vec<uint64_t*> inv_dom;
  vec<char*> inv_dom_saved;
    
  // These are safe under backtracking, so don't need to be trailed.
  int* match;     // Matching variable -> value.
  int* inv_match; // For each value, which variable does it match?
  uint64_t* unmatched; // Which values are not the image of a match?
  
    // Transient state
  uint64_t* rseen;
  uint64_t* seen;
  int* pred;

  int* match_queue;  // size dom_sz (since dom_sz >= sz).
  int* queue_tl;
  // For queuing now-unmatched values.
  int* repair_queue; // size dom_sz.
  int* repair_tl;

  uint64_t* touched; // Which variables had modified domains?

  // Temporary datastructures for Tarjan's scc algorithm.
  int* dfs_num;
  int* lowlink;
  int dfs_count;
  int* stack;
  int* stack_tl;
  bool* on_stack;

  // Recording SCCs for explanation.
  int* sccs; // Variables, ordered by SCC.
  int* scc_idx; // Cross reference to position in sccs.
  int* scc_root;  // Where does the SCC containing x begin?

    // Cached explanation information
    vec<ex_info> exs;
    char exs_saved;
};

bool alldiff_dc::trim_unmatched(int& scc_begin, int scc_end) {
  int* var_tl = match_queue;
  for(int b = 0; b < req_words(dom_sz); ++b) {
    // Iterate over b, in case there are no unmatched
    // values.
    uint64_t unmatched_b(unmatched[b]);
    if(!unmatched_b) continue;
      
    for(int v : range(&sccs[scc_begin], &sccs[scc_end])) {
      if(rseen[block(v)] & bit(v)) continue;
      if(dom[v][b] & unmatched_b) {
        rseen[block(v)] |= bit(v);
        *var_tl = v; ++var_tl;
      }
    }
  }
  // If nothing reached an unmatched value, don't do anything.
  if(var_tl == match_queue) return true;

  int* var_hd = match_queue;
  for(; var_hd != var_tl; ++var_hd) {
    int v = *var_hd;
    int c = match[v];

    // Enqueue anything unseen in inv_dom[c].
    int base = 0;
    uint64_t* c_inv(inv_dom[c]);
    for(int b = 0; b < req_words(sz); ++b) {
      uint64_t word(c_inv[b] & ~rseen[b]);
      if(word) {
        Iter_Word(base, word, [this, &var_tl](int u) {
            *var_tl = u; ++var_tl;
          });
        rseen[b] |= c_inv[b];
      }
    }
  }
  int scc_sz = var_tl - match_queue;
  if(scc_sz == scc_end - scc_begin) {
    scc_begin = scc_end;
    memset(rseen, 0, sizeof(uint64_t) * req_words(sz));
    return true;
  }

  // At this point, we've got everything which can reach unmatched
  // values. Everything else must be in a different SCC.
  int end = scc_begin + scc_sz;
  trail_change(s->persist, scc_root[scc_begin], end);

  int idx = scc_begin;
  for(int v : range(match_queue, var_tl)) {
    int c = match[v];
    seen[block(c)] |= bit(c);

    // Update sccs[] and scc_index[] arrays.
    int rep = sccs[idx];
    int rpos = scc_idx[v];
    sccs[idx] = v;
    sccs[rpos] = rep;
    scc_idx[v] = idx;
    scc_idx[rep] = rpos;
    ++idx;
  }

  // Now trim the domains.
  // This is a bit trickier than the normal (SCC) case, because scc_root[] might not have
  // been set for some reachable values.
  for(unsigned b = 0; b < req_words(dom_sz); ++b) {
    uint64_t forbidden = ~(seen[b] | unmatched[b]);

    for(int z : range(match_queue, var_tl)) {
      uint64_t to_remove(dom[z][b] & forbidden);

      if(to_remove) {
        // Still remove match[z] from dom, even if we're not enqueueing it.
        trail_save(s->persist, dom[z][b], dom_saved[z][b]);
        dom[z][b] &= ~forbidden;
        if(!Forall_Word((b << block_bits()), to_remove, [this,scc_begin,scc_end,end,z](int v) {
              ex_info ex(end, scc_end);
              if(scc_root[scc_idx[inv_match[v]]] != scc_begin) {
                int rbegin(find_scc_begin(inv_match[v]));
                ex = ex_info(rbegin, scc_root[rbegin]);
              }
              return enqueue(*s, xs[z] != v+low, expl<&P::ex_rem>(cast::conv<int>(ex)));
            })) {
          // Cleanup seen and rseen.
          memset(rseen, 0, sizeof(uint64_t) * req_words(sz));
          memset(seen, 0, sizeof(uint64_t) * req_words(dom_sz));
          return false;
        }
      }
    }
  }
  memset(rseen, 0, sizeof(uint64_t) * req_words(sz));
  memset(seen, 0, sizeof(uint64_t) * req_words(dom_sz));
  scc_begin = end;
  return true;
}

bool alldiff_dc::strongconnect(int x, int& begin) {
  lowlink[x] = dfs_num[x] = ++dfs_count;
  *stack_tl = x; ++stack_tl;
  on_stack[x] = true;

  int x_match(match[x]);
  bool okay = Forall_BV(dom[x], dom[x] + req_words(dom_sz), [this, x, x_match, &begin](int c) {
      if(c != x_match) { // Do we need this check?
        // Should have already run 
        assert(! (unmatched[block(c)] & bit(c)) );

        int y(inv_match[c]);
        if(!dfs_num[y]) {
          if(!strongconnect(y, begin))
            return false;
          lowlink[x] = std::min(lowlink[x], lowlink[y]);
        } else if(on_stack[y]) {
          lowlink[x] = std::min(lowlink[x], dfs_num[y]);
        }
      }
      return true;
    });
  if(!okay)
    return false;

  if(lowlink[x] == dfs_num[x]) {
    // SCC root, pop stuff off the stack.
    int* stack_end(stack_tl);
    int* stack_hd(stack_tl);
    do {
      --stack_hd;
      on_stack[*stack_hd] = false;
    } while(*stack_hd != x);

    int scc_sz = stack_tl - stack_hd;
    if(scc_root[begin] == begin + scc_sz) {
      // This can only occur if begin is the current scc_root, and
      // we've seen the whole thing.
      stack_tl = stack_hd;
      begin = begin + scc_sz;
      return true;
    }
    
    int end = begin + (stack_tl - stack_hd);
    trail_change(s->persist, scc_root[begin], end);
    int idx = begin;
    for(int v : range(stack_hd, stack_tl)) {
      // Update sccs[] and scc_index[] arrays.
      int rep = sccs[idx];
      int rpos = scc_idx[v];
      sccs[idx] = v;
      sccs[rpos] = rep;
      scc_idx[v] = idx;
      scc_idx[rep] = rpos;
      ++idx;

      int c(match[v]);
      rseen[block(v)] |= bit(v);
      seen[block(c)] |= bit(c);
    }
    stack_tl = stack_hd;

    // Now go through variable in the SCC, and scratch any values which
    // are not in seen | unmatched.
    for(unsigned b = 0; b < req_words(dom_sz); ++b) {
      uint64_t forbidden = ~(seen[b] | unmatched[b]);

      for(int z : range(stack_tl, stack_end)) {
        uint64_t to_remove(dom[z][b] & forbidden);
        if(b == block(match[z]))
          to_remove &= ~bit(match[z]);

        if(to_remove) {
          // Still remove match[z] from dom, even if we're not enqueueing it.
          trail_save(s->persist, dom[z][b], dom_saved[z][b]);
          dom[z][b] &= ~forbidden;
          if(!Forall_Word((b << block_bits()), to_remove, [this,z](int v) {
                int rbegin(find_scc_begin(inv_match[v]));
                return enqueue(*s, xs[z] != v+low, expl<&P::ex_rem>(cast::conv<int>(ex_info(rbegin, scc_root[rbegin]))));
              })) {
            // Cleanup seen and rseen.
            memset(rseen, 0, sizeof(uint64_t) * req_words(sz));
            memset(seen, 0, sizeof(uint64_t) * req_words(dom_sz));
            return false;
          }
        }
      }
    }
    // Now clear the inverse domains.
    for(unsigned b = 0; b < req_words(sz); ++b) {
      uint64_t forbidden = ~rseen[b];
      Iter_BV(seen, seen + req_words(dom_sz), [this, b, forbidden](int c) {
          if(inv_dom[c][b] & forbidden) {
            trail_save(s->persist, inv_dom[c][b], inv_dom_saved[c][b]);
            inv_dom[c][b] &= ~forbidden;
          }
        });
    }
    // Finally, zero out seen/rseen.
    memset(rseen, 0, sizeof(uint64_t) * req_words(sz));
    memset(seen, 0, sizeof(uint64_t) * req_words(dom_sz));
    // And update the sub-scc start.
    begin = end;
  }

  return true;
}

bool all_different_int(solver_data* s, const vec<intvar>& xs, patom_t r = at_True) {
  assert(r == at_True);

  int lb(xs[0].lb(s));
  int ub(xs[0].ub(s));
  for(const intvar& x : range(xs.begin()+1, xs.end())) {
    lb = std::min(lb, (int) x.lb(s));
    ub = std::max(ub, (int) x.ub(s));
  }
  if(ub - lb + 1 == xs.size()) {
    // Permutation
    return alldiff_dc::post(s, xs);
    // return alldiff_b::post(s, xs);
  } else {
    return alldiff_dc::post(s, xs);
    // return alldiff_b::post(s, xs);
  }
  // return alldiff_v::post(s, xs);
}

bool all_different_except_0(solver_data* s, const vec<intvar>& xs, patom_t r = at_True) {
  assert(r == at_True);

  return alldiff_ex0_b::post(s, xs);
}

}
#endif
