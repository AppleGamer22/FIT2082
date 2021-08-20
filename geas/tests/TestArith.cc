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

  std::cout << "Testing iabs. Expected: SAT" << std::endl;

  intvar z = s.new_intvar(-10, 10);
  intvar x = s.new_intvar(-10, 10);

  int_abs(sd, z, x); 
  add_clause(sd, x < 0, z < 0);
  add_clause(sd, x >= -5, z <= 5);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    model m(s.get_model());
    fprintf(stdout, "[z, x] ~> [%lld, %lld]\n", m[z], m[x]);
  }
}

void test2(void) {
  solver s;
  solver_data* sd(s.data);

  std::cout << "Testing imul. Expected: SAT" << std::endl;

  intvar z = s.new_intvar(1, 10);
  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 0);

//  add_clause(sd, x < -2, x > 2);
//  add_clause(sd, y < -2, y > 2);

  int_mul(sd, z, x, y);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    model m(s.get_model());
    fprintf(stdout, "[z, x, y] ~> [%lld, %lld, %lld]\n", m[z], m[x], m[y]);
  }
}

void test3(void) {
  solver s;
  solver_data* sd(s.data);

  std::cout << "Testing imul. Expected: SAT" << std::endl;

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);

  patom_t b = s.new_boolvar();

  int_le(sd, y, x, 0, b);
  int_le(sd, x, y, 0, ~b);
  add_clause(sd, ~b, x < 5);
  add_clause(sd, b, x < -5);

  if(!enqueue(*sd, ~b, reason()))
    GEAS_ERROR;
  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    model m(s.get_model());
    fprintf(stdout, "[b, x, y] ~> [%d, %lld, %lld]\n", m.value(b), m[x], m[y]);
  }
}

int main(int argc, char** argv) {
  test1();
  test2();
  test3();

  return 0;
}
