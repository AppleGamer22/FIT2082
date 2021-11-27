#include <iostream>
#include <cstdio>
#include <geas/solver/solver.h>
#include <geas/solver/solver_data.h>

#include <geas/constraints/builtins.h>

using namespace geas;

std::ostream& operator<<(std::ostream& o, const solver::result& r) {
  switch(r) {
    case solver::SAT:
      o << "SAT";
      break;
    case solver::UNSAT:
      o << "UNSAT";
      break;
    default:
      o << "UNKNOWN";
  }
  return o;
}
void test1(void) {
  solver s;
  solver_data* sd(s.data);

  std::cout << "Testing linear. Expected: UNSAT" << std::endl;

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);
  intvar z = s.new_intvar(-10, 10);

  {
    vec<int> ks {-1, 1, 1};
    vec<intvar> xs {z, x, y};
    linear_le(sd, ks, xs, -1);
  }
  {
    vec<int> ks {1, -1, -1};
    vec<intvar> xs {z, x, y};
    linear_le(sd, ks, xs, -1);
  }

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    model m(s.get_model());
    fprintf(stdout, "[z, x, y] ~> [%lld, %lld, %lld]\n", m[z], m[x], m[y]);
  }
}

int main(int argc, char** argv) {
  test1();
  return 0;
}
