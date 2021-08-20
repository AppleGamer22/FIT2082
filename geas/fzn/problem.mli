(** Interface file for a Flatzinc problem *)
(* FIXME: Deal with annotations *)

exception Sym_error of string
exception Type_mismatch
exception Root_failure

type ident = string
(*
type item = ident * (fzn_expr array) 
*)

type ival_id = int
type bval_id = int

(* Just model representation -- not worrying about
 * aliasing/definitions *)
type lbool = LFalse | LUndef | LTrue

type ('iv, 'bv) expr =
  | Ilit of int
  | Ivar of 'iv
  | Blit of bool
  | Bvar of 'bv
  | Set of Dom.t
  | Arr of ('iv, 'bv) expr array

type 'bv bval =
  | Bv_bool of bool
  | Bv_var of 'bv
type 'iv ival =
  | Iv_int of int
  | Iv_var of 'iv
 
val get_int : ('iv, 'bv) expr -> int
val get_bool : ('iv, 'bv) expr -> bool
val get_ivar : ('iv, 'bv) expr -> 'iv
val get_bvar : ('iv, 'bv) expr -> 'bv
val get_array : (('iv, 'bv) expr -> 'a) -> ('iv, 'bv) expr -> 'a array

val get_ival : ('iv, 'bv) expr -> 'iv ival
val get_bval : ('iv, 'bv) expr -> 'bv bval

type ann_expr =
  | Ann_int of int
  | Ann_bool of bool
  | Ann_str of string
  | Ann_set of Dom.t
  | Ann_id of ident
  | Ann_arr of ann_expr array
  | Ann_call of ident * (ann_expr array)

type goal =
  | Satisfy
  | Maximize of ival_id
  | Minimize of ival_id

type fzn_expr = (ival_id, bval_id) expr

type cstr = (ident * (fzn_expr array))
type ival_info = { id : ident ; dom : Dom.t ; ann : ann_expr list }
type model = {
  symbols : (ident, fzn_expr * ann_expr list) Hashtbl.t ;
  ivals : ival_info DynArray.t ;
  bvals : (ident * ann_expr list) DynArray.t ;
  constraints : (cstr * ann_expr list) DynArray.t ;
  mutable objective : (goal * ann_expr list)
}

type t = model

val create : unit -> t
val new_ivar : t -> ident -> Dom.t -> ann_expr list -> ival_id
val new_bvar : t -> ident -> ann_expr list -> bval_id

val dom_of : t -> ival_id -> Dom.t
val dom_meet : t -> ival_id -> Dom.t -> bool

val ann_has_id : ann_expr list -> ident -> bool
val ann_has_call : ann_expr list -> ident -> bool
val ann_call_args : ann_expr list -> ident -> ann_expr array option

(** Bind an identifier to an expression *)
val bind : t -> ident -> fzn_expr -> ann_expr list -> unit
(** Resolve a variable to an expression *)
val resolve : t -> ident -> fzn_expr

(** Post a constraint *)
val post : t -> ident -> fzn_expr array -> ann_expr list -> unit

(** Inspection *)
val expr_bvars : ('iv, 'bv) expr -> 'bv list
val expr_ivars : ('iv, 'bv) expr -> 'iv list

val resolve_ann : t -> ann_expr -> fzn_expr

(** Pretty printing *)
val print_ann : Format.formatter -> ann_expr -> unit
val print : Format.formatter -> t -> unit
