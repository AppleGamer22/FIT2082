#include <iostream>
#include <cstdio>

#include <geas/utils/cast.h>
#include <geas/solver/solver.h>

#if 0
#include <geas/engine/env.h>
#include <geas/engine/trail.h>
#include <geas/engine/solver.h>

#include <geas/vars/boolvar.h>
#include <geas/vars/intvar.h>

int main(int argc, char** argv)
{
  env* e = new env;
  solver s(e);

//  std::cout << &(e->gen_vtrail) << std::endl;

  BVarMan bman(e);
  IVarManager* iman(newIVarMan(e, IV_Lazy));

  IntVar v(iman->newVar(0, 10));

  fprintf(stdout, "lb(v) = %d\n", lb(v));
  
  e->post(v.ge(5), expln());
  fprintf(stdout, "lb(v[>=5]) = %d\n", lb(v));

  if(s.solve() == solver::SAT)
  {
    fprintf(stdout, "SAT\n");
    fprintf(stdout, "{v -> %d}\n", v.value());
  } else {
    fprintf(stdout, "UNSAT\n");
  }

  return 0;
}
#endif

using namespace geas;

void print_touched(solver_data& sd) {
  std::cout << "touched: [" ;
  bool first = true;
  for(int e : sd.persist.touched_preds) {
    std::cout << (first ? "" : ", ") << e;
    first = false;
  }
  std::cout << "]" << std::endl;
}

int main(int argc, char** argv) {
  solver s;

  /*
  float f = -15.3;
  pval_t fp = cast::from_float(f);
  fprintf(stdout, "conv(%e) = %lld\n", f, fp);
  fprintf(stdout, "unconv(%lld) = %e\n", fp, cast::to_float(fp));
  */
  assert(cast::from_float(-10.0) < cast::from_float(10.0));

  intvar x = s.new_intvar(-10, 10);
  intvar y = s.new_intvar(-10, 10);
  fp::fpvar z = s.new_floatvar(-10.0, 10.0);
  fprintf(stdout, "z: [%e, %e]\n", z.lb(s.data), z.ub(s.data));

  solver_data& sd(*s.data);

  add_clause(&sd, x <= -5, x >= 5);
  add_clause(&sd, y <= -5, y >= 8);
  
  if(!propagate(sd))
     GEAS_ERROR;
      
  print_touched(sd);
  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(s.data), x.ub(s.data));
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(s.data), y.ub(s.data));
  fprintf(stdout, "z: [%e, %e]\n", z.lb(s.data), z.ub(s.data));

  std::cout << "Push" << std::endl;
  push_level(&sd);

  enqueue(sd, x >= 0, reason());
   
  if(!propagate(sd))
    GEAS_ERROR;  

  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(s.data), x.ub(s.data));
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(s.data), y.ub(s.data));

  print_touched(sd);

  std::cout << "Push" << std::endl;
  push_level(&sd);

  enqueue(sd, y <= 7, reason());
  if(!propagate(sd))
    GEAS_ERROR;

  print_touched(sd);

  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(s.data), x.ub(s.data));
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(s.data), y.ub(s.data));

  std::cout << "Pop" << std::endl;
  bt_to_level(&sd, 1);

  print_touched(sd);
  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(s.data), x.ub(s.data));
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(s.data), y.ub(s.data));

  std::cout << "Pop" << std::endl;
  bt_to_level(&sd, 0);

  print_touched(sd);
  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(s.data), x.ub(s.data));
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(s.data), y.ub(s.data));

  push_level(&sd);
  enqueue(sd, y >= 0, reason());
  if(!propagate(sd))
    GEAS_ERROR;

  push_level(&sd);
  enqueue(sd, x <= 3, reason());
  if(!propagate(sd))
    GEAS_ERROR;

  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(s.data), x.ub(s.data));
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(s.data), y.ub(s.data));
  fprintf(stdout, "z: [%e, %e]\n", z.lb(s.data), z.ub(s.data));

  push_level(&sd);
  enqueue(sd, z <= 3.0, reason());
  if(!propagate(sd))
    GEAS_ERROR;

  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(s.data), x.ub(s.data));
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(s.data), y.ub(s.data));
  fprintf(stdout, "z: [%e, %e]\n", z.lb(s.data), z.ub(s.data));

  bt_to_level(&sd, 0);

  fprintf(stdout, "x: [%lld, %lld]\n", x.lb(s.data), x.ub(s.data));
  fprintf(stdout, "y: [%lld, %lld]\n", y.lb(s.data), y.ub(s.data));

  return 0;
}
