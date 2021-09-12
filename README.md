# FIT2082 XMAPF (Explainable Multi-Agent Path Finder)
**Question**: Have you ever wondered why your robot swarm takes the paths it takes in order to reach its destination without colliding?

**Answer**: No? I didn't care either, since I don't own any robots. That doesn't mean there aren't people who care. Logistics companies that manage their warehouses with an automated fleet of robots need to predict and troubleshoot the paths their robots take as they roam the warehouse while delivering cargo.

I'm a part of a University research project that is developing an explanation generation system for Multi-Agent Path Plans, built on top of Lazy CBS's [(Gange, Harabor and Stuckey, 2021)](https://ojs.aaai.org/index.php/ICAPS/article/view/3471) database of active constraints.

## Critical Dependencies & Acknowledgements
* Gange, G., Harabor, D. and Stuckey, P.J. (2021). Lazy CBS: Implicit Conflict-Based Search Using Lazy Clause Generation. In: Proceedings of the International Conference on Automated Planning and Scheduling. [online] International Conference on Automated Planning and Scheduling. pp.155–162. Available at: https://ojs.aaai.org/index.php/ICAPS/article/view/3471 [Accessed 6 Aug. 2021].
   * [Lazy CBS' code](https://bitbucket.org/gkgange/lazycbs/src/master/)
* Li, J., Harabor, D., Stuckey, P.J., Ma, H., Gange, G. and Koenig, S. (2021). Pairwise symmetry reasoning for multi-agent path finding search. Artificial Intelligence, [online] 301, p.103574. Available at: https://www.sciencedirect.com/science/article/pii/S0004370221001259?via%3Dihub [Accessed 27 Aug. 2021].
* Gange, G. (2018). `geas`. Bitbucket. https://bitbucket.org/gkgange/geas/src/master/

## Queries
### Query Parameters
* path length
* vertex
* time
* agent
* edge (expressed as 2 adjacent locations)

### Example Queries
* `agent(0), edge((3, 2), (3, 3)), time(4)`
* `agent(1), vertex(1, 2), time(7), len(10)`
* `agent(0), len(8)`

## Dependencies
### Debian Linux
```
sudo apt install build-essential gcc g++ make ocaml opam libboost-all-dev libsparsehash-dev
```
### Arch Linux
```
sudo pacman -S base-devel gcc make ocaml ocaml-compiler-libs opam boost boost-libs sparsehash
```
### Required Steps
1. Run: `opam init`
2. Append to your `.bashrc`/`.zshrc`: `eval "$(opam config env)"`
3. Run: `opam install camlidl`
