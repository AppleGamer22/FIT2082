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
#include<boost/tokenizer.hpp>


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

int main(int argc, char** argv) {

  // Reading arguments ----------------------------------------------------------------
  string map_fname, agents_fname, hwy_fname, search_method, results_fname;
  /* double w_hwy = 1.0 , w_focal = 1.0 */;
  int rrr_it, time_limit;  // random restarts iterations number
  int agents_upto;
  bool tweakGVal, rand_succ_gen;
  bool opt_makespan;
  bool opt_anytime;
  try {
    options_description desc("Options");
    desc.add_options() 
      ("help", "Print help messages")
      ("map", value<string>(&map_fname)->required(), "Map filename")
      ("agents", value<string>(&agents_fname)->required(), "Agents filename")
      ("upto", value<int>(&agents_upto)->default_value(INT_MAX), "Number of agents to read (expects movingai format).")
      // ("highway", value<string>(&hwy_fname)->required(), "Highway filename or CRISSCROSS / GM / HONG")
      //("focal_w", value<double>(&w_focal)->default_value(1), "Focal weight")
      //("highway_w", value<double>(&w_hwy)->default_value(1), "Highway weight")
      ("search", value<string>(&search_method)->default_value("ECBS"), "Search method (ECBS or iECBS. Default is ECBS)")
      ("makespan", value<bool>(&opt_makespan)->default_value(false), "Optimize makespan, rather than cost (Default false)")
      ("anytime", value<bool>(&opt_anytime)->default_value(false), "Use anytime cost optimization.")
      ("tweakGVal", value<bool>(&tweakGVal)->default_value(false), "Change the cost structure or not (deprecated)")
      ("rand_succ_gen", value<bool>(&rand_succ_gen)->default_value(false), "Random order of successors generation (in the low-level search)")
      ("RRR", value<int>(&rrr_it)->default_value(0), "Random Restart #iterations (Default is 0, which runs once from root node for agentse ordered sequentially)")
      ("export_results", value<string>(&results_fname)->default_value("NONE"), "Results filename")
      ("time_limit",value<int>(&time_limit)->default_value(300), "Time limit cutoff [seconds]")
      ;

    variables_map vm;
    store(parse_command_line(argc, argv, desc), vm);
    if (vm.count("help")) { 
      cout << endl << desc << endl;
      return 0;
    }
    notify(vm);
  } catch(boost::program_options::required_option& e) {
    cout << endl << e.what() << endl;
    cout << "Use --help for arguments info." << endl << endl;
    return 0;
  }
  catch (exception& e) {
    cerr << endl << e.what() << endl;
    cout << "Use --help for arguments info." << endl << endl;
    return -1;
  }
  // ---------------------------------------------------------------------------------- 

//cout << std::boolalpha<< rand_succ_gen << endl;

  // In case we get timed out during initialisation.

  std::clock_t start(std::clock());

  set_handlers();
  // read the map file and construct its two-dim array

  MapLoader ml = MapLoader(map_fname);
  
  // read agents' start and goal locations
  AgentsLoader al(agents_upto < INT_MAX ? read_movingai(agents_fname, agents_upto) : AgentsLoader(agents_fname));

  // read the egraph (egraph file, experience_weight, weigthedastar_weight)
  EgraphReader egr;
/*
  if (hwy_fname.compare("CRISSCROSS") == 0) {
    egr = EgraphReader();
    egr.createCrissCrossHWY(&ml);
  } else if (hwy_fname.compare("GM") == 0) {
    LearnGMHWY* lgmhwy = new LearnGMHWY(map_fname, agents_fname);
    egr = *(lgmhwy->getHWY(1, w_hwy, 1));  // #iterations=1, w_hwy(=1 for first iteration), w_focal=1
  } else if (hwy_fname.compare("HONG") == 0) {
    HongHWY* honghwy = new HongHWY(map_fname, agents_fname);
    egr = *(honghwy->getHWY(100000,0.5,1.2,1.3));  // (#iterations, alpha, beta, gamma)
  } else {  // filename
*/
    // egr = EgraphReader(hwy_fname);
//  }

#if 0
  cout << /*search_method */ "geas-mapf" << " ; "
       << map_fname << " ; "
       << agents_fname << " ; "
       << al.num_of_agents << " ; "
       // << hwy_fname << " ; "
       // << w_hwy << " ; "
       // << w_focal << " ; ";
       ;
#endif
    //       << std::boolalpha << tweakGVal << " ; ";
  //  cout << "PATH FOUND ; COST ; LB ; HL-EXP ; HL-GEN ; LL-EXP ; LL-GEN ; TIME[s]" << endl;
  //fflush(stdout);
  mapf::MAPF_Solver mapf(ml, al, egr, 1e8);

  //ofstream res_f;
  //res_f.open(results_fname, ios::app);  // append the results file

  //bool res;
  //cout << rrr_it << " ; ";

  clear_handlers();
	// ECBSSearch ecbs = ECBSSearch(ml, al, egr, w_hwy, w_focal, tweakGVal, rrr_it, rand_succ_gen);
	// ecbs.time_limit_cutoff = time_limit;
  // bool res = ecbs.runECBSSearch();
  // ecbs.printPaths();
  bool okay = false;
  try {
    if(terminated)
      throw mapf::MAPF_Solver::SolveAborted {};

    // bool res = mapf.minimizeCost();
    okay = opt_makespan ? MAPF_MinMakespan(mapf) : MAPF_MinCost(mapf);
    // bool res = MAPF_MinMakespan(mapf);
  } catch (mapf::MAPF_Solver::SolveAborted& s) {
    // fprintf(stderr, "%% Solve aborted.\n");
  }
  if(okay)
    mapf.printPaths(stdout);

  fprintf(stderr, "lazy-cbs ; %s ; %s ; %d ; %s ; %.02lf ; ", map_fname.c_str(), agents_fname.c_str(), al.num_of_agents,
    okay ? "done" : "timeout", 1000.0 * (std::clock() - start) / CLOCKS_PER_SEC);
  mapf.printStats(stderr);
  fprintf(stderr, "\n");
}
