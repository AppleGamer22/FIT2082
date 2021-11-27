(* Dealing with systems of definitions. *)

type val_id = int

type irel = Ile | Ieq | Igt | Ine

type 'a def = 
  (* Boolean functions *)
  | Bv_const of bool
  | Bv_neg of 'a
  | At of 'a * irel * int
  | Bv_or of 'a array
  | Bv_and of 'a array
  (* Integer functions *)
  | Iv_const of int
  | Iv_opp of 'a
  (* Arithmetic functions *)
  | Iv_sum of 'a array
  | Iv_prod of 'a array
  | Iv_max of 'a array
  | Iv_min of 'a array
  | Iv_b2i of 'a
  | Elem of 'a array * 'a

type def_id = int
type var_def =
  | Alias of val_id
  | Def of val_id def list

type t

val create : int -> t
val equal : t -> val_id -> val_id -> unit
val bind : t -> val_id -> val_id def -> unit
val extract : t -> var_def array
