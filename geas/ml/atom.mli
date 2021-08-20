(* File generated from atom.idl *)

type pred_t = int32
and pval_t = int64
and struct_1 = {
  pid: int32;
  value: int64;
}
and atom = struct_1

type pred = pred_t
type t = atom
external neg : atom -> atom
	= "camlidl_atom_neg"

external to_int : int64 -> int64
	= "camlidl_atom_to_int"

external inv : int64 -> int64
	= "camlidl_atom_pval_inv"

val at_True : atom
val at_False : atom
