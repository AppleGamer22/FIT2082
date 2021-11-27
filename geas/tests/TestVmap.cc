#include <iostream>

#include <geas/solver/solver.h>
#include <geas/solver/solver_data.h>
#include <geas/engine/persist.h>
#include <geas/engine/valmap.h>

using namespace geas;

int main(int argc, char** argv) {
  /*
  valmap_t<int> valmap(0, 10, VS_Hash);

  for(int ii = 0; ii < 50; ii++)
    valmap.insert(5*ii, ii);
  std::cout << "Table cap: " << valmap.capacity() << std::endl;
  
  int val;
  for(int ii = 0; ii < 100; ii++) {
    if(valmap.lookup(ii, val)) {
      std::cout << ii << " ~> " << val << std::endl;
    }
  }
  */
  return 0;
}
