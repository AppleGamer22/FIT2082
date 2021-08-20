(* File generated from builtins.idl *)

type struct_16 = {
  start: Solver.intvar;
  dur: int;
  res: int;
}
and task = struct_16
and enum_17 =
  | Table_Clause
  | Table_Elem
  | Table_CT
  | Table_Default
and table_mode = enum_17
and table_id = int

val linear_le : Solver.t -> Atom.t -> (int * Solver.intvar) array -> int -> bool
val linear_ne : Solver.t -> Atom.t -> (int * Solver.intvar) array -> int -> bool
val slice_linear_le : Solver.t -> Atom.t -> (int * Solver.intslice) array -> int -> bool
external atmost_1 : Solver.solver -> Atom.atom -> Atom.atom array -> bool
	= "camlidl_builtins_atmost_1"

external atmost_k : Solver.solver -> Atom.atom -> Atom.atom array -> int -> bool
	= "camlidl_builtins_atmost_k"

val bool_linear_le : Solver.t -> Atom.t -> Solver.intvar -> (int * Atom.t) array -> int -> bool
val bool_linear_ge : Solver.t -> Atom.t -> Solver.intvar -> (int * Atom.t) array -> int -> bool
val bool_linear_ne : Solver.t -> Atom.t -> (int * Atom.t) array -> int -> bool
external int_mul : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar -> Solver.intvar -> bool
	= "camlidl_builtins_int_mul"

external int_div : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar -> Solver.intvar -> bool
	= "camlidl_builtins_int_div"

external int_abs : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar -> bool
	= "camlidl_builtins_int_abs"

external int_max : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar array -> bool
	= "camlidl_builtins_int_max"

external int_le : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar -> int -> bool
	= "camlidl_builtins_int_le"

external int_ne : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar -> bool
	= "camlidl_builtins_int_ne"

external int_eq : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar -> bool
	= "camlidl_builtins_int_eq"

external int_element : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar -> int array -> bool
	= "camlidl_builtins_int_element"

external var_int_element : Solver.solver -> Atom.atom -> Solver.intvar -> Solver.intvar -> Solver.intvar array -> bool
	= "camlidl_builtins_var_int_element"

external all_different_int : Solver.solver -> Solver.intvar array -> bool
	= "camlidl_builtins_all_different_int"

external all_different_except_0 : Solver.solver -> Solver.intvar array -> bool
	= "camlidl_builtins_all_different_except_0"

val cumulative :   Solver.t -> (Solver.intvar * int * int) array -> int -> bool
val cumulative_var :   Solver.t -> (Solver.intvar * Solver.intvar * Solver.intvar) array -> Solver.intvar -> bool
val cumulative_float :   Solver.t -> (Solver.intvar * int * float) array -> float -> bool
val disjunctive :   Solver.t -> (Solver.intvar * int) array -> bool
val bipartite_flow :   Solver.t -> int array -> int array -> (Atom.t * int * int) array -> bool
external precede_chain_int : Solver.solver -> Solver.intvar array -> bool
	= "camlidl_builtins_precede_chain_int"

external precede_int : Solver.solver -> int -> int -> Solver.intvar array -> bool
	= "camlidl_builtins_precede_int"

external build_table : Solver.solver -> int -> int array -> table_id
	= "camlidl_builtins_build_table"

external table : Solver.solver -> table_id -> Solver.intvar array -> table_mode -> bool
	= "camlidl_builtins_table"

