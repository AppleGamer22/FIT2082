#include <geas/engine/state.h>
#include <geas/vars/intvar.h>

namespace geas {

void log_state(pred_state& p) {
  int pi = 0;
  fprintf(stderr, "~~~~~~~~~~~~~~~\n");
  for(int ii = 0; ii < p.p_vals.size(); pi++, ii += 2) {
#ifdef PVAL_32
    fprintf(stderr, "p%d : [%d, %d]\n",
      pi, to_int(p.p_vals[ii]), to_int(pval_max - p.p_vals[ii+1]));
#else
    fprintf(stderr, "p%d : [%lld, %lld]\n",
      pi, to_int(p.p_vals[ii]), to_int(pval_max - p.p_vals[ii+1]));
#endif
    // fprintf(stderr, "p%d : [%d, %d]\n",
  }
  fprintf(stderr, "~~~~~~~~~~~~~~~\n");
}

}
