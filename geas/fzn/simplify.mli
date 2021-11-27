(** Problem simplification *)
type bval_id = int
type ival_id = int

type kind = 
  | Bool
  | Int of Dom.t

type irel = Ile | Ieq | Igt | Ine

type ('b, 'i) idef = 
  | Iv_none
  | Iv_const of int
  (* Aliasing *)
  | Iv_eq of 'i
  | Iv_opp of 'i
  (* Arithmetic functions *)
  | Iv_elem of ('i array * 'i)
  | Iv_lin of (int * 'i) array * int
  | Iv_prod of 'i array
  | Iv_max of 'i array
  | Iv_min of 'i array
  | Iv_b2i of 'b

type ('b, 'i) bdef =
  | Bv_none
  | Bv_const of bool
  | Bv_eq of 'b
  | Bv_neg of 'b
  | At of 'i * irel * int
  | Bv_or of 'b array
  | Bv_and of 'b array

type idefn = (bval_id, ival_id) idef
type bdefn = (bval_id, ival_id) bdef

val string_of_bdefn : bdefn -> string
val string_of_idefn : idefn -> string

type t = ((idefn array) * (bdefn array) * Problem.t)


val simplify : Problem.t -> t

val map_idef : ('b -> 'fb) -> ('i -> 'fi) -> ('b, 'i) idef -> ('fb, 'fi) idef
val map_bdef : ('b -> 'fb) -> ('i -> 'fi) -> ('b, 'i) bdef -> ('fb, 'fi) bdef

val log_reprs : idefn array -> bdefn array -> unit
