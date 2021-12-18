#include "map_loader.h"
#include "agents_loader.h"
#include "egraph_reader.h"
#include <lazycbs/mapf/mapf-solver.h>

#include <string>
#include <cstring>
#include <fstream>
#include <ctime>
#include <iostream>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <cstdlib>
#include <cmath>
#include <utility>
#include <boost/program_options.hpp>
#include <boost/tokenizer.hpp>
#include <boost/format.hpp>
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>

namespace py = pybind11;

#ifndef EXTRA_PEN
#define EXTRA_PEN 0  /* Off by default. */
#endif

/* This flag controls early solver termination */
volatile static sig_atomic_t terminated = 0;

/* The signal handler just sets the flag. */
void catch_int (int sig) {
  terminated = 1;
  // signal (sig, catch_int);
}
void set_handlers(void) {
  signal(SIGINT, catch_int);
}
void clear_handlers(void) {
  signal(SIGINT, SIG_DFL);
}


using namespace boost::program_options;
using namespace std;

AgentsLoader read_movingai(std::string fname, int upto) {
  AgentsLoader al;

  string line;
  ifstream myfile(fname.c_str());
  
  if (myfile.is_open()) {
    boost::char_separator<char> sep("\t");
    /*
    tokenizer< char_separator<char> > tok(line, sep);
    tokenizer< char_separator<char> >::iterator beg=tok.begin();
    */
    std::getline(myfile,line); // Ditch the first line
    for (int i=0; i < upto; i++) {
      std::getline(myfile, line);
      boost::tokenizer< boost::char_separator<char> > col_tok(line, sep);
      boost::tokenizer< boost::char_separator<char> >::iterator c_beg=col_tok.begin();
      // EX: 64	brc202d.map	530	481	446	403	444	182	259.12489166
      ++c_beg; // Length
      ++c_beg; // Map
      ++c_beg; // Rows
      ++c_beg; // Cols
      
      // The maps have been padded, so 'real' cells are still indexed from one.
      int c_s = atoi((*c_beg).c_str())+1; ++c_beg;
      int r_s = atoi((*c_beg).c_str())+1; ++c_beg;
      int c_e = atoi((*c_beg).c_str())+1; ++c_beg;
      int r_e = atoi((*c_beg).c_str())+1; ++c_beg;

      al.addAgent(r_s, c_s, r_e, c_e);
    }
    myfile.close();
  }
  else
    cerr << "Agents file not found." << std::endl;
  return al;
}

/*
This function accepts the map path, scenario, agent count and constraints.

The constarints are in the form (agent, ((row1, column1), (row2, column2)), time, cost).

Null locations must have both row and column negative.

Null time must be negative

Null cost must be negative

Agent must be non-negative

If time is negative and at least one location is not nullish, Lazy CBS will return a path where the provided agent does not visit the given location(s).
*/
string init(string map, string scenario, int agentsCount, vector<tuple<int, tuple<tuple<int, int>, tuple<int, int>>, int ,int>> assumptions) {
  bool opt_makespan = false;
  std::clock_t start(std::clock());
  set_handlers();
  MapLoader ml = MapLoader(map);
  
  AgentsLoader al(agentsCount < INT_MAX ? read_movingai(scenario, agentsCount) : AgentsLoader(scenario));

  // read the egraph (egraph file, experience_weight, weigthedastar_weight)
  EgraphReader egr;
  mapf::MAPF_Solver mapf(ml, al, egr, 1e8);
  clear_handlers();
  bool okay = false;
  try {
    if(terminated)
      throw mapf::MAPF_Solver::SolveAborted {};

    // bool res = mapf.minimizeCost();
    okay = opt_makespan ? MAPF_MinMakespan(mapf) : MAPF_MinCost(mapf, assumptions);
    // bool res = MAPF_MinMakespan(mapf);
  } catch (mapf::MAPF_Solver::SolveAborted& s) {
    // fprintf(stderr, "%% Solve aborted.\n");
  }
  fprintf(stderr, "lazy-cbs ; %s ; %s ; %d ; %s ; %.02lf ; ", map.c_str(), scenario.c_str(), al.num_of_agents, okay ? "done" : "timeout", 1000.0 * (std::clock() - start) / CLOCKS_PER_SEC);
  mapf.printStats(stderr);
  if (okay) {
    std::ostringstream output;
    output << boost::format("Map: %s\n") % map;
    output << mapf.printPaths();
    return output.str();
  } else return "not found";
}

PYBIND11_MODULE(lazycbs, m) {
  m.doc() = "XMAPF + Lazy CBS engine";
  // string map, string scenario, int agent, tuple<int, int> locations, int* time, int* cost, bool forbidden
  m.def(
    "init",
    &init,
    "A function which initiates the pathfinding/explanation engine.",
    py::arg("map"),
    py::arg("scenario"),
    py::arg("agentsCount"),
    py::arg("assumptions"),
    py::return_value_policy::copy
  );
}
