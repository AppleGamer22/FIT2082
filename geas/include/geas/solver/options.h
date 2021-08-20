#ifndef GEAS_SOLVER_OPTIONS_H
#define GEAS_SOLVER_OPTIONS_H

#ifdef __cplusplus
extern "C" {
#endif

/*
  options(void)
    // : learnt_dbmax(10000), learnt_growthrate(1.02),
    : learnt_dbmax(50000), learnt_growthrate(1.02),
    // : learnt_dbmax(3), learnt_growthrate(1.5),
      pred_act_inc(0.01), pred_act_growthrate(1.05),
      learnt_act_inc(0.01), learnt_act_growthrate(1.05),
      restart_limit(1000), restart_growthrate(1.05)
      // restart_limit(INT_MAX), restart_growthrate(1.00)
      // restart_limit(10000), restart_growthrate(1.05)
      // restart_limit(2), restart_growthrate(1.5)
  { } 
  */

typedef struct {
  int learnt_dbmax; 
  double learnt_growthrate;

  double pred_act_inc;
  double pred_act_growthrate; 

  double learnt_act_inc;
  double learnt_act_growthrate;

  int restart_limit;
  double restart_growthrate;

  int one_watch;
  int global_diff;

  int eager_threshold;
} options;

typedef struct {
  double time;
  int conflicts;
} limits;

// static const options default_options = options();
extern options default_options;
extern limits no_limit;

#ifdef __cplusplus
}
#endif

#endif
