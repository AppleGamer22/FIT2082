(* File generated from solver.idl *)

type enum_2 =
  | SAT
  | UNSAT
  | UNKNOWN
and result = enum_2
and enum_3 =
  | VAR_INORDER
  | VAR_FIRSTFAIL
  | VAR_LEAST
  | VAR_GREATEST
and var_choice = enum_3
and enum_4 =
  | VAL_MIN
  | VAL_MAX
  | VAL_SPLIT
and val_choice = enum_4
and struct_5 = {
  conflicts: int;
  restarts: int;
  solutions: int;
  time: float;
  num_learnts: int;
  num_learnt_lits: int;
}
and statistics = struct_5
and struct_6 = {
  learnt_dbmax: int;
  learnt_growthrate: float;
  pred_act_inc: float;
  pred_act_growthrate: float;
  learnt_act_inc: float;
  learnt_act_growthrate: float;
  restart_limit: int;
  restart_growthrate: float;
  one_watch: bool;
  global_diff: bool;
  eager_threshold: int;
}
and options = struct_6
and struct_7 = {
  max_time: float;
  max_conflicts: int;
}
and limits = struct_7
and solver
and model
and intvar
and intslice
and fpvar
and brancher

type t  = solver
external default_options : unit -> options
	= "camlidl_solver_default_opts"

external new_solver : options -> solver
	= "camlidl_solver_new_solver"

external solver_id : solver -> int
	= "camlidl_solver_solver_id"

external new_int_brancher : var_choice -> val_choice -> intvar array -> brancher
	= "camlidl_solver_new_int_brancher"

external new_bool_brancher : var_choice -> val_choice -> Atom.atom array -> brancher
	= "camlidl_solver_new_bool_brancher"

external new_bool_priority_brancher : var_choice -> Atom.atom array -> brancher array -> brancher
	= "camlidl_solver_new_bool_priority_brancher"

external new_int_priority_brancher : var_choice -> intvar array -> brancher array -> brancher
	= "camlidl_solver_new_int_priority_brancher"

external seq_brancher : brancher array -> brancher
	= "camlidl_solver_seq_brancher"

external limit_brancher : brancher -> brancher
	= "camlidl_solver_limit_brancher"

external warmstart_brancher : Atom.atom array -> brancher
	= "camlidl_solver_warmstart_brancher"

external toggle_brancher : brancher array -> brancher
	= "camlidl_solver_toggle_brancher"

external add_brancher : solver -> brancher -> unit
	= "camlidl_solver_add_brancher"

external get_brancher : solver -> brancher
	= "camlidl_solver_get_brancher"

external unlimited : unit -> limits
	= "camlidl_solver_unlimited"

external is_consistent : solver -> bool
	= "camlidl_solver_is_consistent"

external solve : solver -> limits -> result
	= "camlidl_solver_solve"

external abort : solver -> unit
	= "camlidl_solver_abort_solve"

external post_atom : solver -> Atom.atom -> bool
	= "camlidl_solver_post_atom"

external post_clause : solver -> Atom.atom array -> bool
	= "camlidl_solver_post_clause"

external assume : solver -> Atom.atom -> bool
	= "camlidl_solver_assume"

external retract : solver -> unit
	= "camlidl_solver_retract"

external retract_all : solver -> unit
	= "camlidl_solver_retract_all"

external get_conflict : solver -> Atom.t array = "ml_get_conflict"
external new_intvar : solver -> int -> int -> intvar
	= "camlidl_solver_new_intvar"

external permute_intvar : solver -> intvar -> int array -> intvar
	= "camlidl_solver_permute_intvar"

external intvar_neg : intvar -> intvar
	= "camlidl_solver_intvar_neg"

external intvar_plus : intvar -> int -> intvar
	= "camlidl_solver_intvar_plus"

external make_sparse : intvar -> int array -> bool
	= "camlidl_solver_make_sparse"

external new_boolvar : solver -> Atom.atom
	= "camlidl_solver_new_boolvar"

external slice_of_intvar : intvar -> intslice
	= "camlidl_solver_slice_of_intvar"

external slice_from : intslice -> int -> intslice
	= "camlidl_solver_slice_from"

external slice_upto : intslice -> int -> intslice
	= "camlidl_solver_slice_upto"

external slice_rezero : intslice -> int -> intslice
	= "camlidl_solver_slice_rezero"

external new_floatvar : solver -> float -> float -> fpvar
	= "camlidl_solver_new_floatvar"

external set_bool_polarity : solver -> Atom.atom -> bool -> unit
	= "camlidl_solver_set_bool_polarity"

external set_int_polarity : intvar -> bool -> unit
	= "camlidl_solver_set_int_polarity"

external ivar_pred : intvar -> Atom.pred_t
	= "camlidl_solver_ivar_pid"

external ivar_lb : intvar -> int
	= "camlidl_solver_ivar_lb"

external ivar_ub : intvar -> int
	= "camlidl_solver_ivar_ub"

external current_ivar_lb : intvar -> int
	= "camlidl_solver_current_ivar_lb"

external current_ivar_ub : intvar -> int
	= "camlidl_solver_current_ivar_ub"

external get_ivar_activities : solver -> intvar array -> float array = "ml_get_ivar_activities"
external suggest_ivar_value : solver -> intvar -> int
	= "camlidl_solver_suggest_ivar_value"

external get_model : solver -> model
	= "camlidl_solver_get_model"

external int_value : model -> intvar -> int
	= "camlidl_solver_int_value"

external intslice_value : model -> intslice -> int
	= "camlidl_solver_intslice_value"

external float_value : model -> fpvar -> float
	= "camlidl_solver_float_value"

external atom_value : model -> Atom.atom -> bool
	= "camlidl_solver_atom_value"

external ivar_le : intvar -> int -> Atom.atom
	= "camlidl_solver_ivar_le"

external ivar_eq : intvar -> int -> Atom.atom
	= "camlidl_solver_ivar_eq"

external islice_le : intslice -> int -> Atom.atom
	= "camlidl_solver_islice_le"

external fpvar_le : fpvar -> float -> Atom.atom
	= "camlidl_solver_fpvar_le"

external fpvar_lt : fpvar -> float -> Atom.atom
	= "camlidl_solver_fpvar_lt"

external new_pred : solver -> int -> int -> Atom.pred_t
	= "camlidl_solver_new_pred"

external pred_ge : Atom.pred_t -> int -> Atom.atom
	= "camlidl_solver_pred_ge"

external get_statistics : solver -> statistics
	= "camlidl_solver_get_statistics"

external set_cons_id : solver -> int -> unit
	= "camlidl_solver_set_cons_id"

let ivar_lt v k = ivar_le v (k-1)
let ivar_ge v k = Atom.neg (ivar_lt v k)
let ivar_gt v k = Atom.neg (ivar_le v k)
let ivar_ne v k = Atom.neg (ivar_eq v k)
let islice_lt v k = islice_le v (k-1)
let islice_ge v k = Atom.neg (islice_lt v k)
let islice_gt v k = Atom.neg (islice_le v k)
let fpvar_ge v k = Atom.neg (fpvar_lt v k)
let fpvar_gt v k = Atom.neg (fpvar_le v k)
