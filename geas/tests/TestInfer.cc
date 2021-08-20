#include <iostream>

#include <geas/solver/solver.h>
#include <geas/solver/solver_data.h>
#include <geas/engine/persist.h>

using namespace geas;

int main(int argc, char** argv) {
  solver s; 

  solver_data& sd(*s.data);
  geas::pid_t x = new_pred(sd);
  geas::pid_t y = new_pred(sd);
  
  // x >= 5 -> x >= 8.
  add_clause(&sd, ~patom_t(x, 5), patom_t(x, 8));

  if(!enqueue(sd, patom_t(x, 6), reason()))
    GEAS_ERROR;
  if(!enqueue(sd, ~patom_t(x, 10), reason()))
    GEAS_ERROR;

  if(!propagate(sd))
    GEAS_ERROR;

  if(!sd.state.is_entailed(patom_t(x, 8)))
    GEAS_ERROR;
  if(sd.state.is_entailed(patom_t(x, 9)))
    GEAS_ERROR;

  std::cout << "x : [" << sd.state.p_vals[x] << ", " << sd.state.p_vals[x^1] << "]" << std::endl;
  std::cout << "y : [" << sd.state.p_vals[y] << ", " << sd.state.p_vals[y^1] << "]" << std::endl;

  push_level(&sd);

  if(!enqueue(sd, patom_t(y, 8), reason()))
    GEAS_ERROR;

  if(!sd.state.is_entailed(patom_t(y, 5)))
    GEAS_ERROR;
  if(sd.state.is_entailed(patom_t(y, 10)))
    GEAS_ERROR;

//  if(enqueue(sd, ~patom_t(y, 5), reason()))
//    ERROR; 
  if(!propagate(sd))
    GEAS_ERROR;

  std::cout << "x : [" << sd.state.p_vals[x] << ", " << sd.state.p_vals[x^1] << "]" << std::endl;
  std::cout << "y : [" << sd.state.p_vals[y] << ", " << sd.state.p_vals[y^1] << "]" << std::endl;

  bt_to_level(&sd, 0);
  std::cout << "x : [" << sd.state.p_vals[x] << ", " << sd.state.p_vals[x^1] << "]" << std::endl;
  std::cout << "y : [" << sd.state.p_vals[y] << ", " << sd.state.p_vals[y^1] << "]" << std::endl;
  return 0;
}
