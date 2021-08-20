#include <iostream>
#include <geas/solver/solver.h>

using namespace geas;

std::ostream& operator<<(std::ostream& o, solver::result r) {
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

int main(int argc, char** argv) {
  solver s;  

  // Initialize problem
   
  solver::result r = s.solve();

  std::cout << r << std::endl;

  return 0;
};
