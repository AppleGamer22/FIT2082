#ifndef GEAS_STATS_H
#define GEAS_STATS_H

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  // statistics(void) : conflicts(0), restarts(0), solutions(0) { }
  int conflicts;
  int restarts;
  int solutions;
  double time;

  int num_learnts;
  int num_learnt_lits;
} statistics;

#ifdef __cplusplus
}
#endif

#endif
