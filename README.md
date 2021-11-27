# FIT2082 XMAPF (Explainable Multi-Agent Path Finder)
**Question**: Have you ever wondered why your robot swarm takes the paths it takes in order to reach its destination without colliding?

**Answer**: No? I didn't care either, since I don't own any robots. That doesn't mean there aren't people who care. Logistics companies that manage their warehouses with an automated fleet of robots need to predict and troubleshoot the paths their robots take as they roam the warehouse while delivering cargo.

I'm a part of a University research project that is developing an explanation generation system for Multi-Agent Path Plans, built on top of Lazy CBS's [(Gange, Harabor and Stuckey, 2021)](https://ojs.aaai.org/index.php/ICAPS/article/view/3471) database of active constraints.

## Critical Dependencies & Acknowledgements
* Gange, G., Harabor, D. and Stuckey, P.J. (2021). Lazy CBS: Implicit Conflict-Based Search Using Lazy Clause Generation. In: Proceedings of the International Conference on Automated Planning and Scheduling. [online] International Conference on Automated Planning and Scheduling. pp.155–162. Available at: https://ojs.aaai.org/index.php/ICAPS/article/view/3471 [Accessed 6 Aug. 2021].
   * [Lazy CBS' code](https://bitbucket.org/gkgange/lazycbs/src/master/)
* Li, J., Harabor, D., Stuckey, P.J., Ma, H., Gange, G. and Koenig, S. (2021). Pairwise symmetry reasoning for multi-agent path finding search. Artificial Intelligence, [online] 301, p.103574. Available at:https://doi.org/10.1016/j.artint.2021.103574 [Accessed 27 Aug. 2021].
* Gange, G. (2018). `geas`. Bitbucket. https://bitbucket.org/gkgange/geas/src/master/

## Datasets
* The [MovingAI dataset](https://movingai.com/benchmarks/mapf/index.html) is useful for testing MAPF algorithms because of its variety of maps and multi-agent scenario examples. We used the dataset as part of the constraints and barriers output testing of our [modified Lazy CBS code](https://github.com/AppleGamer22/FIT2082), and as the initial user input for the graphical user interface that displays the multi-agent paths and accept queries from the user.
   * Here is the [specification](https://movingai.com/benchmarks/formats.html) of the dataset's map and scenario files. Due to the critical dependency of Lazy CBS on ECBS, the map files from Moving AI must be converted to the ECBS format using [this Python 2 script](https://bitbucket.org/gkgange/lazycbs/src/master/scripts/map-conv.py) that was written by one of my project supervisors, Graeme Gange.

## Software Tools
* [Lazy CBS](https://bitbucket.org/gkgange/lazycbs/src/master/) is the backend MAPF algorithm of this project's explanation engine, written by one of my project supervisors, Graeme Gange.
* We used [`pybind11`](https://pybind11.readthedocs.io/en/stable/) in order to enable the (compiled) [modified Lazy CBS code](https://github.com/AppleGamer22/FIT2082) to be called from the [GUI's python code](https://github.com/puggxlii/FIT2082MAPF).

## Tutorials & Articles
* The <http://mapf.info/> website is a great resource that showcases great MAPF research papers, tutorials, software and benchmarks.
* Gange, G., Harabor, D. and Stuckey, P.J. (2021). Lazy CBS: Implicit Conflict-Based Search Using Lazy Clause Generation. In: Proceedings of the International Conference on Automated Planning and Scheduling. [online] International Conference on Automated Planning and Scheduling. pp.155–162. Available at: https://ojs.aaai.org/index.php/ICAPS/article/view/3471 [Accessed 6 Aug. 2021].
* Li, J., Harabor, D., Stuckey, P.J., Ma, H., Gange, G. and Koenig, S. (2021). Pairwise symmetry reasoning for multi-agent path finding search. Artificial Intelligence, [online] 301, p.103574. Available at: https://doi.org/10.1016/j.artint.2021.103574 [Accessed 27 Aug. 2021].
* Sharon, G., Stern, R., Felner, A. and Sturtevant, N.R. (2015). Conflict-based search for optimal multi-agent pathfinding. Artificial Intelligence, [online] 219(1), pp.40–66. Available at: https://doi.org/10.1016/j.artint.2014.11.006 [Accessed 11 Aug. 2021].
* Stern, R., Sturtevant, N., Felner, A., Koenig, S., Ma, H., Walker, T., Li, J., Atzmon, D., Cohen, L., Kumar, T.K.S., Boyarski, E. and Bartak, R. (2019). Multi-Agent Pathfinding: Definitions, Variants, and Benchmarks. [online] arXiv.org. Available at: https://arxiv.org/abs/1906.08291 [Accessed 13 Aug. 2021].

## Queries
### Query Parameters
* path length
* vertex
* time
* agent
* edge (expressed as 2 adjacent locations)

## Debugging
* In the following example, the `lazycbs` binary is debugged with `gdb`.
   * It is checked if Agent 1 can be forced to traverse through `(3, 3)` while going to its target location.
   * This check must run from the `lazycbs` directory.

```bash
gdb --args python3 -c 'from lazycbs import init; print(init("../maps/debug-6-6.map.ecbs", "../scenarios/debug-6-6-2-2.scen", 2, [(1, ((3, 3), (-1, -2)), -4, -100)]))'
```

## Dependencies
### Debian Linux
```bash
sudo apt install build-essential gcc g++ make ocaml opam libboost-all-dev libsparsehash-dev python3-dev pybind11-dev python3-pybind11
```
### Arch Linux
```bash
sudo pacman -S base-devel gcc make ocaml ocaml-compiler-libs opam boost boost-libs sparsehash python pybind11
```

### Compiling
1. Make sure you have a working Debian-based/Arch-based Linux installation
2. Install the [dependencies](#dependencies) for your Linux distribution
3. Run: `opam init`
4. Append to the end of your `.bashrc`/`.zshrc`: `eval "$(opam config env)"`
5. Run `source ~/.bashrc`
6. Run: `opam install camlidl`
7. Clone this repository with either of the following procedures:
   * Run `git clone https://github.com/AppleGamer22/FIT2082.git` in your terminal
   * Run `gh repo clone AppleGamer22/FIT2082` in your terminal
   * Download the repository manually through GitHub's website
8. Change directory to the root directory of this project
9.  Run `make build` to compile the binary.
   * If running `make build` fails, please try to run `make clean` and run `make build`
11. 
12. To run the debugging example without a GUI:
```bash
$ cd lazycbs
$ python3 -c 'from lazycbs import init; print(init("../maps/debug-6-6.map.ecbs", "../scenarios/debug-6-6-2-2.scen", 2, [(1, ((2, 4), (-1, -2)), -2, -100)]))'
```