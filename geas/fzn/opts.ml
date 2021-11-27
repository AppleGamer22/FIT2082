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

let infile = ref None
let outfile = ref None
let verbosity = ref 0

let print_stats = ref Suppress
let quiet = ref false

let max_solutions = ref 1
let free = ref false
let pol = ref true
let half_reify = ref false

let restart_limit = ref None
(* let conflict_limit = ref 0 *)
let limits = ref (Solver.unlimited ())

let obj_probe_limit = ref None
let core_opt = ref false
let core_ratio = ref None

let core_harden = ref false

let core_selection = ref Violation
let core_reformulation = ref ReformEach
let core_type = ref IntCore
let core_factor_coeff = ref true

let one_watch = ref true
let global_diff = ref false

let check = ref false

let native = ref false

(* --------------------------------------------- *)
(*       Specification list for options          *)
(* --------------------------------------------- *)
let (speclist:(Arg.key * Arg.spec * Arg.doc) list) =
  Arg.align
    [(
      "--verbosity",
      Arg.Set_int(verbosity),
      "<int> : verbosity level, from 0 to 2 (default:0)"
     ) ;
     (
      "-s",
      Arg.Unit (fun () -> print_stats := Compact),
      " : print statistics"
     ) ;
     (
      "--verbose-stats",
      Arg.Unit (fun () -> print_stats := Verbose),
      " : report statistics in a more readable form."
     ) ;
     (*
     (
      "-o",
      Arg.String (fun s -> outfile := Some s),
      "<string> : file to write transformed model"
     ) ;
     *)
     (
       "-q",
       Arg.Unit (fun () -> quiet := true),
       " : suppress printing of model"
     ) ;
     (
      "--check",
      Arg.Unit (fun () -> check := true),
      " : check solutions"
     ) ;
     (
      "-f",
      Arg.Unit (fun () -> free := true),
      " : free search"
     ) ;
     (*
     (
      "-pol",
      Arg.Bool (fun b -> pol := b),
      " : use polarity analysis"
     ) ;
     (
      "-half-reif",
      Arg.Bool (fun b -> half_reify := b),
      " : use polarity analysis"
     ) ;
     *)
     (
       (* "-nof_solutions", *)
       "-n",
       Arg.Int (fun k -> max_solutions := k),
       " : maximum number of solutions to report"
     ) ;
     (
      "--obj-probe",
      Arg.Int (fun k -> obj_probe_limit := Some k),
      " : number of conflicts to give speculative objective tightening."
     ) ;
     (
      "--one-watch",
      Arg.Bool (fun b -> one_watch := b),
      " : use one-literal watching for learnt clauses (default: true)."
     ) ;
     (
      "--global-diff",
      Arg.Bool (fun b -> global_diff := b),
      " : use global difference-logic propagator to handle (reified) inequalities (default: false)."
     ) ;
     (
      "--core-opt",
      Arg.Set core_opt,
      " : use an unsat-core driven optimization."
     ) ;
     (
      "--core-ratio",
      Arg.Float (fun r -> core_ratio := Some r),
      " : how much of the resource budget to spend on core-driven optimization."
     ) ;
     (
      "--core-harden",
      Arg.Bool (fun b -> core_harden := b),
      " : whether to attempt to harden bounds during unsat core iterations (default: false)."
     ) ;
     (
       "--core-type",
       Arg.Symbol (["int" ; "slice"], fun s ->
         core_type := match s with
           | "int" -> IntCore
           | "slice" -> SliceCore
           | s -> failwith (Format.sprintf "ERROR: Unexpected core type \"%s\"" s)),
       " : choose the type of unsat-core reformulation (default: int).") ;
     (
      "--factor-coeff",
      Arg.Bool (fun b -> core_factor_coeff := b),
      " : whether to factor coefficients during unsat core iterations (default: true)."
     ) ;
     (
      "--reformulate",
      Arg.Tuple
        [
          Arg.Symbol (["uniform" ; "violation" ; "weight" ; "weight-violation"], fun s ->
            core_selection := match s with
            | "uniform" -> Uniform
            | "violation" -> Violation
            | "weight" -> Weight
            | "weight-violation" -> WeightViolation
            | s -> failwith (Format.sprintf "ERROR: Unexpected core selection policy \"%s\"" s)) ;
          Arg.Symbol (["one" ; "each" ; "eager"], fun s ->
            core_reformulation := match s with
            | "one" -> ReformOne
            | "each" -> ReformEach
            | "eager" -> ReformEager
            | s -> failwith (Format.sprintf "ERROR: Unknown reformulation policy \"%s\"" s)) ],
      " : choose the core reformulation strategy."
     ) ;
     (
      "-a",
      Arg.Unit (fun () -> max_solutions := 0),
      " : find all solutions"
     ) ;
     (
      "-r",
      Arg.Int (fun r -> restart_limit := Some r),
      "<int> : initial restart limit"
     ) ;
     (
      "-c",
      Arg.Int (fun c -> limits := {!limits with Solver.max_conflicts = c }),
      "<int> : maximum number of conflicts"
     ) ;
     (
      "--time-out",
      Arg.Int (fun t -> limits := {!limits with Solver.max_time = float_of_int t }),
      "<int> : maximum time (in seconds)"
     );
     (
      "-t",
      Arg.Int (fun t -> limits := {!limits with Solver.max_time = (float_of_int t) /. 1000. }),
      "<int> : maximum time (in millisecond)"
     );
    ]
