type stats_mode = 
  | Suppress
  | Compact
  | Verbose

type core_select =
  | Uniform
  | Violation
  | Weight
  | WeightViolation

type reform_mode =
  | ReformOne
  | ReformEach
  | ReformEager

type core_type =
  | IntCore
  | SliceCore

val infile : string option ref
val outfile : string option ref

val verbosity : int ref

val quiet : bool ref

val max_solutions : int ref

val print_stats : stats_mode ref
val free : bool ref
val pol : bool ref
val half_reify : bool ref

val restart_limit : int option ref
(* val conflict_limit : int ref *)
val limits : Solver.limits ref
val obj_probe_limit : int option ref
val core_opt : bool ref
val core_ratio : float option ref
val core_type : core_type ref
val core_factor_coeff : bool ref

val core_harden : bool ref
val core_selection : core_select ref
val core_reformulation : reform_mode ref

val one_watch : bool ref
val global_diff : bool ref

val check : bool ref

val native : bool ref

(* --------------------------------------------- *)
(*       Specification list for options          *)
(* --------------------------------------------- *)
val speclist : (Arg.key * Arg.spec * Arg.doc) list ;;
