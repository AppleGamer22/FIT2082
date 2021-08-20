(* File generated from internal.idl *)

type struct_8 = {
  ic: int;
  ix: Solver.intvar;
}
and int_linterm = struct_8
and struct_9 = {
  sc: int;
  sx: Solver.intslice;
}
and slice_linterm = struct_9
and struct_10 = {
  ac: int;
  ax: Atom.atom;
}
and at_linterm = struct_10
and struct_11 = {
  ds: Solver.intvar;
  dd: int;
}
and dtask = struct_11
and struct_12 = {
  cs: Solver.intvar;
  cd: int;
  cr: int;
}
and task = struct_12
and struct_13 = {
  vs: Solver.intvar;
  vd: Solver.intvar;
  vr: Solver.intvar;
}
and vtask = struct_13
and struct_14 = {
  fs: Solver.intvar;
  fd: int;
  fr: float;
}
and ftask = struct_14
and struct_15 = {
  at: Atom.atom;
  src: int;
  sink: int;
}
and bp_flow = struct_15

external linear_le : Solver.solver -> Atom.atom -> int_linterm array -> int -> bool
	= "camlidl_internal_linear_le"

external linear_ne : Solver.solver -> Atom.atom -> int_linterm array -> int -> bool
	= "camlidl_internal_linear_ne"

external slice_linear_le : Solver.solver -> Atom.atom -> slice_linterm array -> int -> bool
	= "camlidl_internal_slice_linear_le"

external bool_linear_le : Solver.solver -> Atom.atom -> Solver.intvar -> at_linterm array -> int -> bool
	= "camlidl_internal_bool_linear_le"

external bool_linear_ge : Solver.solver -> Atom.atom -> Solver.intvar -> at_linterm array -> int -> bool
	= "camlidl_internal_bool_linear_ge"

external bool_linear_ne : Solver.solver -> Atom.atom -> at_linterm array -> int -> bool
	= "camlidl_internal_bool_linear_ne"

external disjunctive : Solver.solver -> dtask array -> bool
	= "camlidl_internal_disjunctive"

external cumulative : Solver.solver -> task array -> int -> bool
	= "camlidl_internal_cumulative"

external cumulative_var : Solver.solver -> vtask array -> Solver.intvar -> bool
	= "camlidl_internal_cumulative_var"

external cumulative_float : Solver.solver -> ftask array -> float -> bool
	= "camlidl_internal_cumulative_float"

external bipartite_flow : Solver.solver -> int array -> int array -> bp_flow array -> bool
	= "camlidl_internal_bipartite_flow"

