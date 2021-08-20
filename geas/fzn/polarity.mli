(** Module for inferring polarity information *)

type vref =
  | Int of Problem.ival_id
  | Bool of Problem.bval_id

type polarity =
  | Pos of vref
  | Neg of vref

type rule =
  | Define of vref
  | Fact of polarity
  | Rule of polarity * polarity

type ctx = { pos : bool ; neg : bool }

type t = { ivars : ctx array ; bvars : ctx array }

val polarity : Simplify.t -> t

val ctx_string : ctx -> string
