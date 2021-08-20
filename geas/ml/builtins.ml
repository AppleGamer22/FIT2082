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

module I = Internal
let to_linterm cx = { I.ic = fst cx; I.ix = snd cx }
let to_slice_linterm cx = { I.sc = fst cx; I.sx = snd cx }
let linear_le s r xs k =   I.linear_le s r (Array.map to_linterm xs) k
let linear_ne s r xs k =   I.linear_ne s r (Array.map to_linterm xs) k
let slice_linear_le s r xs k =   I.slice_linear_le s r (Array.map to_slice_linterm xs) k
external atmost_1 : Solver.solver -> Atom.atom -> Atom.atom array -> bool
	= "camlidl_builtins_atmost_1"

external atmost_k : Solver.solver -> Atom.atom -> Atom.atom array -> int -> bool
	= "camlidl_builtins_atmost_k"

let to_at_linterm cx = { I.ac = fst cx; I.ax = snd cx }
let bool_linear_le s r z xs k =   I.bool_linear_le s r z (Array.map to_at_linterm xs) k
let bool_linear_ge s r z xs k =   I.bool_linear_ge s r z (Array.map to_at_linterm xs) k
let bool_linear_ne s r xs k =   I.bool_linear_ne s r (Array.map to_at_linterm xs) k
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

let cumulative s xs c =   I.cumulative s (Array.map (fun (x, d, r) -> { I.cs = x ; I.cd = d ; I.cr = r }) xs) c
let cumulative_var s xs c =   I.cumulative_var s (Array.map (fun (x, d, r) -> { I.vs = x ; I.vd = d ; I.vr = r }) xs) c
let cumulative_float s xs c =   I.cumulative_float s (Array.map (fun (x, d, r) -> { I.fs = x ; I.fd = d ; I.fr = r }) xs) c
let disjunctive s xs =   I.disjunctive s (Array.map (fun (x, d) -> { I.ds = x ; I.dd = d }) xs)
let bipartite_flow s srcs sinks flows =   I.bipartite_flow s srcs sinks (Array.map (fun (a, sr, de) -> { I.src = sr; I.sink = de; I.at = a }) flows)
external precede_chain_int : Solver.solver -> Solver.intvar array -> bool
	= "camlidl_builtins_precede_chain_int"

external precede_int : Solver.solver -> int -> int -> Solver.intvar array -> bool
	= "camlidl_builtins_precede_int"

external build_table : Solver.solver -> int -> int array -> table_id
	= "camlidl_builtins_build_table"

external table : Solver.solver -> table_id -> Solver.intvar array -> table_mode -> bool
	= "camlidl_builtins_table"

