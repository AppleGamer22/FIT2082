# FIT2082 XMAPF (Explainable Multi-Agent Path Finder)
**Question**: Have you ever wondered why your robot swarm takes the paths it takes in order to reach its destination without colliding?

**Answer**: No? Me neither, I don't own any robots. That doesn't mean there aren't people who cares. Logistics companies that manage their warehouses with an automated fleet of robots need to predict and troubleshoot the paths their robots take as they roam the warehouse while delivering cargo.

I'm a part of a University research project that is developing an explanation generation system for Multi-Agent Path Plans, built on top of Lazy CBS's [(Gange, Harabor and Stuckey, 2021)](https://ojs.aaai.org/index.php/ICAPS/article/view/3471) database of active constraints.

## Critical Dependencies & Acknowledgements
* Gange, G., Harabor, D. and Stuckey, P.J. (2021). Lazy CBS: Implicit Conflict-Based Search Using Lazy Clause Generation. In: Proceedings of the International Conference on Automated Planning and Scheduling. [online] International Conference on Automated Planning and Scheduling. pp.155–162. Available at: https://ojs.aaai.org/index.php/ICAPS/article/view/3471 [Accessed 6 Aug. 2021].
   * [Lazy CBS' code](https://bitbucket.org/gkgange/lazycbs/src/master/)
* Li, J., Harabor, D., Stuckey, P.J., Ma, H., Gange, G. and Koenig, S. (2021). Pairwise symmetry reasoning for multi-agent path finding search. Artificial Intelligence, [online] 301, p.103574. Available at: https://www.sciencedirect.com/science/article/pii/S0004370221001259?via%3Dihub [Accessed 27 Aug. 2021].
* Gange, G. (2018). `geas`. Bitbucket. https://bitbucket.org/gkgange/geas/src/master/


## Ubuntu Dependencies
* `build-essential`
* `gcc`
* `g++`
* `make`
* `ocaml`
  * Run: `opam init`
  * Append to your `.bashrc`: `eval "$(opam config env)"`
  * Run: `opam install camlidl`
* `opam`
* `libboost-all-dev`
* `libsparsehash-dev`