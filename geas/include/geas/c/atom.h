#ifndef GEAS_C_ATOM_H
#define GEAS_C_ATOM_H
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  uint32_t pid;
  uint64_t val;
  // uint32_t val;
} atom;

typedef uint32_t pred_t;
typedef uint64_t pval_t;

atom neg(atom);

pval_t pval_inv(pval_t);
int64_t to_int(pval_t);

#ifdef __cplusplus
}
#endif

#endif
