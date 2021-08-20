# Lazy CBS: A multi-agent pathfinding solver, using a lazy clause generation backend

## Dependencies:
 + [geas](https://bitbucket.org/gkgange/geas)
 
     A lazy clause generation-based constraint programming solver.
     For Lazy CBS, only the C++ library and headers are necessary;
     it is not necessary to build the ML interface for flatzinc wrapper.

 + ECBS
 
     The single-agent pathfinder for Lazy CBS is built on a modified version
     of ECBS. Source is available as a tarball under Downloads.

   Lazy CBS also requires the Boost program options library.

## Building:
  + First, build `libgeas.a` and `libecbs.a` from their respective code bases.
  + In the Makefile, set `GEAS_ROOT` and `ECBS_ROOT` to the location of `geas`
    and `ecbs` respectively.
  + Call `make`, which will build a binary lazy-cbs.

## Acknowledgements
  Many thanks to Liron Cohen, for providing the source to ECBS.
