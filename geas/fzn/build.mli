(* Instantiate a problem in a solver, returning
 * a mapping from problem to solver variables. *)

(* Process-independent atoms *)
type epred =
  | Ptrue
  | Pbool of int
  | Pge of int * int
  | Peq of int * int


type eatom =
  | Pos of epred
  | Neg of epred
 
(* type env = { ivars : Solver.intvar array ; bvars : Atom.atom array } *)

val build_problem : Solver.t -> Simplify.t -> Polarity.t -> Registry.env
val atom_of_eatom : Registry.env -> eatom -> Atom.t

val atom_lookup : Registry.env -> (Atom.t -> eatom option)
