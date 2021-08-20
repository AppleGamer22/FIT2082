Elsie Geas - Another Lazy Clause Generation Solver
==================================================

What's with the name?
---------------------
Well, it's an LCG solver. An *Ell-Cee-Gee* solver. Yeah, that's all it is.
That, and the drive to implement it does have an air of compulsion to it.

Why another solver?
-------------------
The compulsion to build solvers seems to be a bit of an occupational sickness.

But mostly to play around with different implementation ideas. Geas is
intended to be readily extensible (with new variable types as well as
propagators), can cope with large variable domains, and can spawn
multiple solver instances in the same process.

How to build it?
----------------
Requirements:
  * Core engine:
    - C++ compiler (g++/clang++)
  * ML interface, and FZN frontend:
    - `ocaml`
    - `camlidl`

The easiest way to get `camlidl` is using `opam`.

* On OSX:
```sh
brew install ocaml opam
```
* or Ubuntu:
```sh
sudo apt-get install ocaml opam
```
Then, in either case:
```sh
opam init
eval `opam config env`
opam install camlidl
```
Then just call `make` in the root directory of the repository.
This builds the `Flatzinc` frontend `fzn/fzn_geas`.
Afterwards, you can also build the interactive top-level by calling
`make geas_top` in the `ml` subdirectory.
