(** Constraint registry *)
type env = { ivars : Solver.intvar array ; bvars : Atom.atom array }

type expr = (Solver.intvar, Atom.t) Problem.expr

type poster = Solver.t -> expr array -> Problem.ann_expr list -> bool
type raw_poster = Solver.t -> env -> Problem.fzn_expr array -> Problem.ann_expr list -> bool

val initialize : unit -> unit

val register : string -> poster -> unit
val register_raw : string -> raw_poster -> unit
val lookup : string -> raw_poster


val resolve_expr : env -> Problem.fzn_expr -> expr
