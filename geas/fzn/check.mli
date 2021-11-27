(* Check a model *)
exception Not_satisfied of string

val check : Problem.t -> Solver.intvar array -> Atom.t array -> Solver.model -> bool

val check_exn : Problem.t -> Solver.intvar array -> Atom.t array -> Solver.model -> unit
