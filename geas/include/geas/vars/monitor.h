#ifndef GEAS__VARS__MONITOR__H
#define GEAS__VARS__MONITOR__H
#include <geas/engine/propagator.h>
#include <geas/solver/solver_data.h>

namespace geas {

template<class V, class Tag>
class bounds_monitor : public propagator, public prop_inst< bounds_monitor<V, Tag> > {
  typedef bounds_monitor<V, Tag> P;
  typedef prop_inst< bounds_monitor<V, Tag> > I;

  watch_result wake_lb(int x) {
    lb_watched[x] = false;
    lb_change.push(tag[x]);
    return Wt_Drop;
  }
  watch_result wake_ub(int x) {
    ub_watched[x] = false;
    ub_change.push(tag[x]);   
    return Wt_Drop;
  }

  bounds_monitor(solver_data* s)
    : propagator(s) { }

public: 
  bool propagate(vec<clause_elt>& confl) { return true; }

  static bounds_monitor<V, Tag>* create(solver_data* s) {
    return new bounds_monitor<V, Tag>(s); 
  }

  void monitor(V v, Tag t) {
    int vi = vars.size();
    vars.push(v);
    tag.push(t);
    lb_watched.push(true);
    ub_watched.push(true);
    v.attach(s, E_LB, this->template watch<&P::wake_lb>(vi));
    v.attach(s, E_UB, this->template watch<&P::wake_ub>(vi));
  }

  void reset(void) {
    lb_change.clear();
    ub_change.clear();
    for(int ii : irange(vars.size())) {
      if(!lb_watched[ii]) {
        lb_watched[ii] = true;
        vars[ii].attach(s, E_LB, this->template watch<&P::wake_lb>(ii));
      }
      if(!ub_watched[ii]) {
        ub_watched[ii] = true;
        vars[ii].attach(s, E_UB, this->template watch<&P::wake_ub>(ii));
      }
    }
  }
  
  const vec<Tag>& updated_lbs(void) const { return lb_change; }
  const vec<Tag>& updated_ubs(void) const { return ub_change; }

protected:
  vec<V> vars;
  vec<Tag> tag;
  vec<bool> lb_watched;
  vec<bool> ub_watched;

  vec<Tag> lb_change;
  vec<Tag> ub_change;
};

}

#endif
