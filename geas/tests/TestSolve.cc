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

  std::cout << "Testing element. Expected: SAT" << std::endl;
  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);
  intvar z = s.new_intvar(-10, 10);

  solver_data* sd(s.data);

  add_clause(sd, x <= 3, y <= 2);
  add_clause(sd, x >= 5, y >= 5);

//  add_clause(sd, x >= 0, z >= 0);
//  add_clause(sd, z >= 0, y >= 0);

  vec<int> ks = {1, 3, 5, 9, 10};   
  int_element(sd, x, y, ks);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    fprintf(stdout, "[x, y, z] ~> [%lld, %lld, %lld]\n", x.lb(s.data), y.lb(s.data), z.lb(s.data));
  }
}

void test2(void) {
  solver s;

  std::cout << "Testing conflict analysis. Expected: UNSAT" << std::endl;

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);
  intvar z = s.new_intvar(-10, 10);

  solver_data* sd(s.data);

  add_clause(sd, x > 0, y > 0, z > 0);
  add_clause(sd, x > 0, y > 0, z <= 0);
  add_clause(sd, x > 0, y < 0, z > 0);
  add_clause(sd, x > 0, y < 0, z < 0);
  add_clause(sd, x < 0, y > 0, z > 0);
  add_clause(sd, x < 0, y > 0, z < 0);
  add_clause(sd, x < 0, y < 0, z > 0);
  add_clause(sd, x < 0, y < 0, z < 0);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    fprintf(stdout, "[x, y, z] ~> [%lld, %lld, %lld]\n", x.lb(s.data), y.lb(s.data), z.lb(s.data));
  }
}

void test3(void) {
  solver s;

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 8);
  intvar z = s.new_intvar(-10, 5);

  solver_data* sd(s.data);

  vec<intvar> args = {y, z};
  int_max(sd, x, args);

  vec<int> ks = {1, -1};
  vec<intvar> xs = {y, z};
  // vec<intvar> xs = {x, z};
  linear_le(sd, ks, xs, -1);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    fprintf(stdout, "[x, y, z] ~> [%lld, %lld, %lld]\n", x.lb(s.data), y.lb(s.data), z.lb(s.data));
  }
}

void test4(void) {
  solver s;

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 8);
  intvar z = s.new_intvar(-10, 5);
  fp::fpvar u = s.new_floatvar(-10, 5);

  solver_data* sd(s.data);

//  vec<intvar> args = {y, z};
  int_mul(sd, z, x, y);
  add_clause(sd, u >= 2.5, x >= 3);
  add_clause(sd, u >= 2.5, x < 3);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    fprintf(stdout, "[x, y, z, u] ~> [%lld, %lld, %lld, %e]\n", x.lb(s.data), y.lb(s.data), z.lb(s.data), u.lb(s.data));
    model m(s.get_model());
    fprintf(stdout, "[x, y, z, u] ~> [%lld, %lld, %lld, %e]\n", m[x], m[y], m[z], m[u]);
    if(m.value(x >= 3))
      fprintf(stdout, "x >= 3\n");
    if(m.value(x >= 12))
      fprintf(stdout, "x >= 12\n");
    if(m.value(x <= 12))
      fprintf(stdout, "x <= 12\n");
  }
}

void test5(void) {
  solver s;
  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);

  solver_data* sd(s.data);

  // add_clause(sd, x == 3, y == 3);
  // add_clause(sd, x == 3, y < 2);
  add_clause(sd, x >= 3, y >= 3);
  add_clause(sd, x <= 3, y >= 3);
  add_clause(sd, x >= 3, y <= 3);
  add_clause(sd, x <= 3, y <= 3);
  
  add_clause(sd, x >= 3, y < 2);
  add_clause(sd, x <= 3, y < 2);

  add_clause(sd, x > 4, y < 1);

  solver::result r = s.solve();
  std::cout << "Result: " << r << std::endl;

  if(r == solver::SAT) {
    model m(s.get_model());
    fprintf(stdout, "[x, y] ~> [%lld, %lld]\n", m[x], m[y]);
  }
}

int main(int argc, char** argv) {
//  test1();
  test2();
  test3();
  test4();
  test5();

  return 0;
}
