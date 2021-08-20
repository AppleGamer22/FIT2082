#ifndef GEAS_MAPF__SOLVER_H
#define GEAS_MAPF__SOLVER_H
// ECBS includes
#include "map_loader.h"
#include "agents_loader.h"

// geas includes
#include <geas/solver/solver.h>
#include <geas/utils/bitset.h>

#include <lazycbs/mapf/agent-pf.h>

namespace mapf {

class MAPF_Solver {
 public:
  struct SolveAborted { };

  struct penalty {
    geas::pid_t p;
    geas::pval_t lb;
  };
  
  struct cons_key {
    int timestamp;
    int loc1;
    int loc2;
  };
  struct cons_key_hasher {
    size_t operator()(const cons_key& k) const {
      size_t h(5331);
      h = ((h<<5) + k.timestamp)^h;
      h = ((h<<5) + k.loc1)^h;
      h = ((h<<5) + k.loc2)^h;
      return h;
    }
  };
  struct cons_key_eq {
    bool operator()(const cons_key& x, const cons_key& y) const {
      return x.timestamp == y.timestamp && x.loc1 == y.loc1 && x.loc2 == y.loc2;
    }
  };
    
  enum BarrierDir { UP = 0, LEFT = 1, DOWN = 2, RIGHT = 3 };

  struct barrier_key {
    int agent;
    BarrierDir dir; 
    int location;
    int time_at_edge;
  };
  struct barrier_data {
    geas::patom_t act; 
    int start;
    int duration;
  };

  struct barrier_key_hasher {
    size_t operator()(const barrier_key& k) const {
      size_t h(5331);
      h = ((h<<5) + k.agent)^h;
      h = ((h<<5) + (size_t) k.dir)^h;
      h = ((h<<5) + k.location)^h;
      h = ((h<<5) + k.time_at_edge)^h;
      return h;
    }
  };
  struct barrier_key_eq {
    bool operator()(const barrier_key& x, const barrier_key& y) const {
      return x.agent == y.agent && x.dir == y.dir && x.location == y.location && x.time_at_edge == y.time_at_edge;
    }
  };

  enum ConflictType { C_MUTEX, C_BARRIER };
  struct barrier_info {
    int s_loc; // Start corner
    int e_loc; // Exit corner
  };
  struct conflict {
    conflict(void) { }

    conflict(int _timestamp, int _a1, int _a2, int _loc1, int _loc2)
      : timestamp(_timestamp), type(C_MUTEX)
      , a1(_a1), a2(_a2), p({_loc1, _loc2}) { }

    conflict(int _timestamp, int _a1, int _a2, int _loc1, int _loc2, bool dummy)
      : timestamp(_timestamp), type(C_BARRIER)
      , a1(_a1), a2(_a2), b({_loc1, _loc2}) { }
    /*
    conflict(int _timestamp, int _a1, int _a2, int h_loc, int v_loc, int r_loc)
      : timestamp(_timestamp), type(C_BARRIER)
      , a1(_a1), a2(_a2), b({h_loc, v_loc, r_loc}) { }
      */

    static conflict barrier(int t, int a1, int a2, int loc1, int loc2) {
      conflict c(t, a1, a2, loc1, loc2, false);
      return c;
    }

    int timestamp;
    ConflictType type;

    int a1;
    int a2;
     
    union {
      struct {
        int loc1;
        int loc2;
      } p;
      barrier_info b;
    };
  };

  struct cons_data {
    intvar sel; // Selector variable
    btset::bitset attached; // Which agents are already attached?
  };

  MAPF_Solver(const MapLoader& ml, const AgentsLoader& al, const EgraphReader& egr, int cost_ub);

  // Problem information
  const MapLoader* ml;
  const AgentsLoader* al;
  const EgraphReader* egr;
  const int map_size;

  // Solver engine
  geas::solver s;

  // Single-agent search engines
  vec<Agent_PF*> pathfinders;

  // For conflict checking
  vec<bool> reservation_table;
  vec<int> cmap; // Map at the current time
  vec<int> nmap; // Map at the next time

  // Constraints?
  vec<cons_data> constraints;
  vec< vec<barrier_data> > barriers;
  std::unordered_map<cons_key, int, cons_key_hasher, cons_key_eq> cons_map;
  std::unordered_map<barrier_key, int, barrier_key_hasher, barrier_key_eq> barrier_map;
  // conflict new_conflict;
  vec<conflict> new_conflicts;
  p_sparseset agent_set;

  // For unsat-core reasoning
  vec<penalty> penalties;
  std::unordered_map<geas::pid_t, int> penalty_table;
  int cost_lb;
  int cost_ub;

  // How many high-level conflicts have been processed?
  int HL_conflicts;

  inline int row_of(int loc) const { return loc / ml->cols; }
  inline int col_of(int loc) const { return loc % ml->cols; }

  int maxPathLength(void) const;

  // Search for some feasible plan, given a set of assumptions.
  bool buildPlan(vec<geas::patom_t>& assumps);
  bool minimizeCost();
//   bool minimizeMakespan();
  void printPaths(FILE* f = stdout) const;
  void printStats(FILE* f = stdout) const;
   
  bool runUCIter(void);
  bool checkForConflicts(void);
  // In buildPlan, we also try to apply bypasses.
  bool resolveConflicts(void);
  bool addConflict(void);
  bool processCore(vec<geas::patom_t>& core);
      
  geas::patom_t getBarrier(int ai, BarrierDir dir, int t0, int p0, int dur);
  bool checkBarrierViolated(int ai, int t, int p, int delta, int dur) const;

  int monotoneSubchainStart(int dy, int dx, int ai, int t) const;
  int monotoneSubchainEnd(int dy, int dx, int ai, int t) const;

  std::pair<int, bool*> retrieve_reservation_table(int ai);

  ~MAPF_Solver();
};

bool MAPF_MinCost(MAPF_Solver& s);
bool MAPF_MinMakespan(MAPF_Solver& s);
bool MAPF_MaxDeadlines(MAPF_Solver& s);

}

#endif
