#ifndef GEAS_BOUNDS_H
#define GEAS_BOUNDS_H
#include<algorithm>

template<class T>
struct interval {
  T lb; T ub; 

  bool empty(void) const { return ub < lb; }

  interval operator&(const interval& o) const {
    return interval { std::max(lb, o.lb), std::min(ub, o.ub) };
  }
  interval& operator&=(const interval& o) {
    lb = std::max(lb, o.lb); ub = std::min(ub, o.ub);
    return *this;
  }

  interval operator|(const interval& o) const {
    return interval { std::min(lb, o.lb), std::max(ub, o.ub) };  
  }
  interval& operator|=(const interval& o) {
    lb = std::min(lb, o.lb); ub = std::max(ub, o.ub);
    return *this;
  }

  interval operator-(void) const {
    return interval { -ub, -lb };
  }
  interval operator+(const interval& o) const {
    return interval { lb + o.lb, ub + o.ub };
  }

  bool elem(const T& x) const { return lb <= x && x <= ub; }
};

template<class T>
interval<T> pos(const interval<T>& o) {
  return interval<T> { std::max((T) 1, o.lb), o.ub };
}

template<class T>
interval<T> neg(const interval<T>& o) {
  return interval<T> { o.lb, std::min((T) (-1), o.ub) };
}

template<class T>
interval<T> nonneg(const interval<T>& o) {
  return interval<T> { std::max((T) 0, o.lb), o.ub };
}

template<class T>
interval<T> nonpos(const interval<T>& o) {
  return interval<T> { o.lb, std::min((T) 0, o.ub) };
}

typedef interval<int64_t> int_itv;
// typedef interval<int32_t> int_itv;

#endif
