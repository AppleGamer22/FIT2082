#ifndef GEAS__DIFFLOGIC__H
#define GEAS__DIFFLOGIC__H
#include <geas/solver/solver_data.h>
#include <geas/vars/intvar.h>

namespace geas {

namespace difflogic {
  // r -> (x - y <= k)
  bool post(solver_data* s, patom_t r, intvar x, intvar y, int k);
  bool check_sat(solver_data* s, intvar x, intvar y, int k);
  bool check_sat(solver_data* s, ctx_t& ctx, intvar x, intvar y, int k);
}

}

#endif
