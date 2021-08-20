module S = Stream
module H = Hashtbl
module Dy = DynArray
module L = List

module U = Util

open Token
module P = FznParser

module Pr = Problem
module Simp = Simplify
module Pol = Polarity

module Sol = Solver
module At = Atom

module B = Builtins

open Build
open Registry

exception Unknown_constraint of string

let put = Format.fprintf

let print_atom problem env =
  (* Build translation table *)
  let ivar_names = H.create 17 in
  let atom_names = H.create 17 in
  Dy.iteri (fun idx info ->
    H.add ivar_names (Sol.ivar_pred env.ivars.(idx)) info.Pr.id
  ) problem.Pr.ivals ;
  Dy.iteri (fun idx (id, _) -> H.add atom_names env.bvars.(idx) id) problem.Pr.bvals ;
  (* Now, the actual function *)
  (fun fmt at ->
    try
      let id = H.find ivar_names at.At.pid in
      Format.fprintf fmt "%s >= %s" id (Int64.to_string @@ At.to_int at.At.value)
    with Not_found -> try
      let id = H.find ivar_names (Int32.logxor at.At.pid Int32.one) in
      Format.fprintf fmt "%s <= %s" id (Int64.to_string @@ At.to_int @@ At.inv at.At.value)
    with Not_found -> try
      let id = H.find atom_names at in
      Format.fprintf fmt "%s" id
    with Not_found -> try
      let id = H.find atom_names (At.neg at) in
      Format.fprintf fmt "not %s" id
    with Not_found ->
      Format.fprintf fmt "x%d >= %s" (Int32.to_int at.At.pid) (Int64.to_string @@ At.to_int at.At.value))

let ivar_name problem env =
  (* Build translation table *)
  let ivar_names = H.create 17 in
  Dy.iteri (fun idx info ->
    H.add ivar_names env.ivars.(idx) info.Pr.id
  ) problem.Pr.ivals ;
  (* Now, the actual function *)
  (fun x ->
    try H.find ivar_names x
    with Not_found -> Format.sprintf "x%d" (Int32.to_int (Sol.ivar_pred x)))

let print_nogood problem env =
  let pp_atom = print_atom problem env in
  (fun fmt nogood ->
    (* Util.print_array ~pre:"%% @[[" ~post:"]@]@." ~sep:",@ " pp_atom fmt nogood *)
    Util.print_array ~pre:"%% NOGOOD: " ~post:"@." ~sep:", " pp_atom fmt nogood
  )

(* Replace variable identifiers with the corresponding
 * intvar/atom *)
let rec resolve_expr env expr =
  match expr with
  | Pr.Ilit v -> Pr.Ilit v
  | Pr.Ivar iv -> Pr.Ivar env.ivars.(iv)
  | Pr.Blit b -> Pr.Blit b
  | Pr.Bvar bv -> Pr.Bvar env.bvars.(bv)
  | Pr.Set dom -> Pr.Set dom
  | Pr.Arr es -> Pr.Arr (Array.map (resolve_expr env) es)

(* Evaluate an expression under a model *)
let rec eval_expr env model expr =
  match expr with
  | Pr.Ilit v -> Pr.Ilit v
  | Pr.Ivar iv -> Pr.Ilit (Sol.int_value model env.ivars.(iv))
  | Pr.Blit b -> Pr.Blit b
  | Pr.Bvar bv -> Pr.Blit (Sol.atom_value model env.bvars.(bv))
  | Pr.Set dom -> Pr.Set dom
  | Pr.Arr es -> Pr.Arr (Array.map (eval_expr env model) es)

let expr_array = function
  | Pr.Arr es -> es
  | _ -> failwith "Expected array" 
               
let get_var_branch ann =
  match ann with
  | Pr.Ann_id "input_order" -> Sol.VAR_INORDER
  | Pr.Ann_id "first_fail" -> Sol.VAR_FIRSTFAIL
  | Pr.Ann_id "smallest" -> Sol.VAR_LEAST
  | Pr.Ann_id "largest" -> Sol.VAR_GREATEST
  | _ -> (* failwith "Unknown var-branch annotation." *)
    (* let _ = Format.fprintf Format.err_formatter "%% WARNING: Unknown var-branch annotation, ignoring.@." in *)
    Sol.VAR_INORDER

let get_val_branch ann =
  match ann with
  | Pr.Ann_id "indomain_min" -> Sol.VAL_MIN
  | Pr.Ann_id "indomain_max" -> Sol.VAL_MAX 
  | Pr.Ann_id "indomain_split" -> Sol.VAL_SPLIT
  | Pr.Ann_id ("indomain"|"default") -> Sol.VAL_MIN
  | _ -> failwith "Unknown val-branch annotation."

let get_ann_array f ann =
  match ann with
  | Pr.Ann_arr xs -> Array.map f xs
  | _ -> failwith "Expected annotation array."

let collect_array_ivars env expr =
  let vars = 
    match expr with
    | Pr.Arr es ->
      List.rev @@ Array.fold_left (fun vs e ->
        match e with
        | Pr.Ivar v -> env.ivars.(v) :: vs
        | _ -> vs) [] es
    | _ -> failwith "Expected array in collect_array_ivars"
    in
    Array.of_list vars

let force_array_ivars env solver expr =
  match expr with
  | Pr.Arr es -> Array.map (fun e ->
    match e with
    | Pr.Ivar v -> env.ivars.(v)
    | Pr.Ilit k -> Solver.new_intvar solver k k
    | _ -> failwith "Expected value of int-kind in force_array_ivars") es
  | _ -> failwith "Expected array argument to force_array_ivars"

let collect_array_bvars env expr =
  let vars = 
    match expr with
    | Pr.Arr es ->
      List.rev @@ Array.fold_left (fun vs e ->
        match e with
        | Pr.Bvar v -> env.bvars.(v) :: vs
        | _ -> vs) [] es
    | _ -> failwith "Expected array in collect_array_ivars"
    in
    Array.of_list vars

let force_array_bvars env expr =
  match expr with
  | Pr.Arr es -> Array.map (fun e ->
    match e with
    | Pr.Bvar v -> env.bvars.(v)
    | Pr.Blit b -> if b then At.at_True else At.neg At.at_True
    | _ -> failwith "Expected bool-sorted term in force_array_bvars"
    ) es
  | _ -> failwith "Expected array argument to force_array_bvars"

let is_search_ann ann =
  match ann with
  | Pr.Ann_call (("seq_search"|"int_search"|"bool_search"|"bool_priority"|"int_priority"), _) -> true
  | _ -> false

let rec parse_branching problem env solver ann =
  match ann with  
  | Pr.Ann_call ("seq_search", args) | Pr.Ann_call ("warm_start_array", args) ->
      let sub = get_ann_array (fun x -> x) args.(0) in
      Sol.seq_brancher (Array.map (parse_branching problem env solver) sub)
  | Pr.Ann_call ("int_search", args) ->
      let varb = get_var_branch args.(1) in
      let valb = get_val_branch args.(2) in
      let vars = collect_array_ivars env (Pr.resolve_ann problem args.(0)) in
      Sol.new_int_brancher varb valb vars
  | Pr.Ann_call ("bool_search", args) ->
      let varb = get_var_branch args.(1) in
      let valb = get_val_branch args.(2) in
      let vars = collect_array_bvars env (Pr.resolve_ann problem args.(0)) in
      Sol.new_bool_brancher varb valb vars
  | Pr.Ann_call ("int_priority", args) ->
    let varb = get_var_branch args.(2) in
    let sel = force_array_ivars env solver (Pr.resolve_ann problem args.(0)) in
    let sub = get_ann_array (parse_branching problem env solver) args.(1) in
    Sol.new_int_priority_brancher varb sel sub
  | Pr.Ann_call ("bool_priority", args) ->
    let varb = get_var_branch args.(2) in
    let sel = force_array_bvars env (Pr.resolve_ann problem args.(0)) in
    let sub = get_ann_array (parse_branching problem env solver) args.(1) in
    Sol.new_bool_priority_brancher varb sel sub
  | Pr.Ann_call ("warm_start", args) ->
    let xs = force_array_ivars env solver (Pr.resolve_ann problem args.(0)) in
    let cs = Pr.get_array Pr.get_int (Pr.resolve_ann problem args.(1)) in
    assert (Array.length xs = Array.length cs) ;
    Sol.warmstart_brancher
      (Array.init (Array.length xs) (fun i -> Sol.ivar_eq xs.(i) cs.(i)))
  | _ -> failwith "Unknown search annotation"

let rec parse_branchings problem env solver anns =
  let rec aux acc anns =
    match anns with
    | [] -> List.rev acc
    | ann :: anns' ->
      if is_search_ann ann  then
        aux (parse_branching problem env solver ann :: acc) anns'
      else
        aux acc anns'
  in
  aux [] anns

(* Returns none if failed *)
let get_array_assumps env in_acc arr =
  let r_assumps = Array.fold_left
    (fun acc elt ->
      match acc, elt with
      | None, _ -> None
      | _, Pr.Blit false -> None
      | Some assumps, Pr.Blit true -> Some assumps
      | Some assumps, Pr.Bvar b -> Some (env.bvars.(b) :: assumps)
      | _ -> failwith "Non-bool in assumption.") (Some in_acc) arr in
  r_assumps

let get_ann_assumps problem env anns =
  let rec aux acc anns =
    match anns with
    | [] -> Some (List.rev acc)
    | ((Pr.Ann_call ("assume", args)) :: anns') -> 
      begin
        match get_array_assumps env acc
                (Pr.get_array (fun x -> x) (Pr.resolve_ann problem args.(0))) with
        | None -> None
        | Some acc' -> aux acc' anns'
      end
    | _ :: anns' -> aux acc anns'
  in aux [] anns
 
let build_branching problem env solver anns =
  let wrap b =
    if !Opts.free then
      Sol.toggle_brancher [|b; Sol.get_brancher solver|]
    else
      b
  in
  match parse_branchings problem env solver anns with
  | [] -> ()
  | [b] ->  Sol.add_brancher solver (wrap b)
  | bs ->
    let b = Sol.seq_brancher (Array.of_list bs) in
     Sol.add_brancher solver (wrap b)

(* Helpers for printing arrays *)
let print_fzn_array p_expr fmt es dims =
(*
  Format.fprintf fmt "array%dd(@[" (Array.length dims) ;
  Util.print_array Pr.print_ann ~sep:",@ " ~pre:"@[" ~post:"@]" fmt dims ;
  Format.fprintf fmt ",@ " ;
  Util.print_array p_expr ~sep:",@ " ~pre:"[@[" ~post:"@]]" fmt es ;
  Format.fprintf fmt "@])"
  *)
  Format.fprintf fmt "array%dd(" (Array.length dims) ;
  Util.print_array Pr.print_ann ~sep:", " ~pre:"" ~post:"" fmt dims ;
  Format.fprintf fmt ", " ;
  Util.print_array p_expr ~sep:", " ~pre:"[" ~post:"]" fmt es ;
  Format.fprintf fmt ")"


(* Print a variable assignment *)
let get_array_dims e_anns =
  match Pr.ann_call_args e_anns "output_array" with
  | Some [| Pr.Ann_arr dims |] -> dims
  | _ -> failwith "Malformed array dimensions"

let print_binding fmt id expr e_anns =
  let rec aux fmt expr =
    match expr with
    | Pr.Ilit v -> Format.pp_print_int fmt v
    | Pr.Blit b -> Format.pp_print_string fmt (if b then "true" else "false")
    | Pr.Arr es -> print_fzn_array aux fmt es (get_array_dims e_anns)
          (* Util.print_array ~sep:"," ~pre:"[@[" ~post:"@]]" aux fmt es *)
    | _ -> failwith "Expected only literals in solution"
  in
  Format.fprintf fmt "%s = " id ;
  aux fmt expr ;
  Format.fprintf fmt ";@."

let is_output problem expr e_anns =
  match expr with
  | Pr.Ivar iv ->
     let info = Dy.get problem.Pr.ivals iv in
     Pr.ann_has_id info.Pr.ann "output_var"
  | Pr.Bvar bv ->
     let (_, ann) = Dy.get problem.Pr.bvals bv in
     Pr.ann_has_id ann "output_var"
  | Pr.Arr _ -> Pr.ann_has_call e_anns "output_array"
  | _ -> false
  
let is_output_id problem id =
  try
    let (_, anns) = Hashtbl.find problem.Pr.symbols id in
    Pr.ann_has_id anns "output_var" || Pr.ann_has_call anns "output_array"    
  with Not_found -> false

let print_solution fmt problem env model =
  if !Opts.check then
    Check.check_exn problem env.ivars env.bvars model
  else () ;
  Hashtbl.iter (fun id (expr, anns) ->
                if is_output_id problem id || is_output problem expr anns then
                  print_binding fmt id (eval_expr env model expr) anns
                else
                  ()) problem.Pr.symbols

let keys tbl = Hashtbl.fold (fun k v ks -> k :: ks) tbl []
let values tbl = Hashtbl.fold (fun k v vs -> v :: vs) tbl []

let output_vars problem env : (Sol.intvar list) * (Atom.t list) =
  let out_ivars = H.create 17 in
  let out_bvars = H.create 17 in
  (* Recursively collect vars in an expression *)
  let rec collect_expr expr =
    match expr with
    | Pr.Ivar iv -> H.replace out_ivars iv env.ivars.(iv)
    | Pr.Bvar bv -> H.replace out_bvars bv env.bvars.(bv)
    | Pr.Arr es -> Array.iter collect_expr es
    | _ -> ()
  in
  (* Collect vars occuring in any output expressions *)
  Hashtbl.iter (fun id (expr, anns) ->
                if is_output problem expr anns then
                  collect_expr expr
                else
                  ()) problem.Pr.symbols ;
  (values out_ivars, values out_bvars)
  
let block_solution problem env =
  let ivars, atoms = output_vars problem env in
  fun solver model ->
  (*
    let iv_atoms =
      List.map (fun x -> Sol.ivar_ne x (Sol.int_value model x)) ivars in 
      *)
    let iv_low =
      List.map (fun x -> Sol.ivar_lt x (Sol.int_value model x)) ivars in
    let iv_high =
      List.map (fun x -> Sol.ivar_gt x (Sol.int_value model x)) ivars in
    let bv_atoms =
      List.map (fun b -> if Sol.atom_value model b then Atom.neg b else b) atoms in
    (* Sol.post_clause solver (Array.of_list (iv_atoms @ bv_atoms)) *)
    Sol.post_clause solver (Array.of_list (iv_low @ (iv_high @ bv_atoms)))
      
let apply_assumps solver assumps =
  let rec aux assumps =
    match assumps with
      | [] -> true
      | at :: assumps' ->  
        if Sol.assume solver at then
          aux assumps'
        else false
  in aux assumps

(*
let print_nogood fmt nogood =
  let print_atom fmt at =
    if (Int32.to_int at.At.pid) mod 2 == 0 then
      Format.fprintf fmt "p%s >= %s"
        (Int32.to_string (Int32.shift_right at.At.pid 1))
        (Int64.to_string (At.to_int at.At.value))
    else
      Format.fprintf fmt "p%s <= %s"
        (Int32.to_string (Int32.shift_right at.At.pid 1))
        (Int64.to_string (At.to_int @@ At.inv at.At.value))
  in
  Util.print_array ~pre:"%% @[[" ~post:"]@]@." print_atom fmt nogood
  *)
    
let solve_satisfy print_model print_nogood solver assumps =
  let fmt = Format.std_formatter in
  if not (apply_assumps solver assumps) then
    begin
      print_nogood fmt (Sol.get_conflict solver) ;
      Format.fprintf fmt "==========@."
    end
  else
    match Sol.solve solver !Opts.limits with
    | Sol.UNKNOWN -> Format.fprintf fmt "=====UNKNOWN=====@."
    | Sol.UNSAT ->
      begin
        if List.length assumps > 0 then
          let nogood = Sol.get_conflict solver in
          print_nogood fmt nogood
      end ; 
      Format.fprintf fmt "=====UNSATISFIABLE=====@."
    | Sol.SAT ->
      print_model fmt (Sol.get_model solver) ;
      Format.fprintf fmt "==========@."

let solve_findall print_model print_nogood block_solution solver assumps =
  let fmt = Format.std_formatter in
  let rec aux max_sols =
    match Sol.solve solver !Opts.limits with
    | Sol.UNKNOWN -> ()
    | Sol.UNSAT -> Format.fprintf fmt "==========@."
    | Sol.SAT ->
       begin
         let model = Sol.get_model solver in
         print_model fmt model ;
         if max_sols <> 1 then
           if block_solution solver model then
             aux (max 0 (max_sols-1))
           else
             Format.fprintf fmt "==========@." 
       end
  in
  if not (apply_assumps solver assumps) then
    Format.fprintf fmt "==========@."
  else
    aux !Opts.max_solutions
          
let decrease_ivar obj_val ivar solver model =
  let model_val = Sol.int_value model ivar in
  (* Format.fprintf Format.err_formatter "%% [[OBJ = %d]]@." model_val ;  *)
  obj_val := Some model_val ;
  Sol.post_atom solver (Sol.ivar_lt ivar model_val)
      
let increase_ivar obj_val ivar solver model =
  let model_val = Sol.int_value model ivar in
  (* Format.fprintf Format.err_formatter "%% [[OBJ = %d]%@." model_val ; *)
  obj_val := Some model_val ;
  Sol.post_atom solver (Sol.ivar_gt ivar model_val)

let relative_limits solver limits =
  let s = Sol.get_statistics solver in
  (* let _ = Format.fprintf Format.err_formatter "Time: %f@, max %f." s.Sol.time limits.Sol.max_time in *)
  { Sol.max_time =
      if limits.Sol.max_time > 0. then
        max 0.001 (limits.Sol.max_time -. s.Sol.time)
      else 0. ;
    Sol.max_conflicts =
      if limits.Sol.max_conflicts > 0 then
        max 1 (limits.Sol.max_conflicts - s.Sol.conflicts)
      else 0 }

let eval_obj m obj =
  match obj with
  | (_, Some (xs, k)) -> Array.fold_left (fun s (c, x) -> s + c * Sol.int_value m x) k xs
  | (x, _) -> Sol.int_value m x

let obj_lt obj obj_val =
  match obj with
  | (x, _) -> Sol.ivar_lt x obj_val

let obj_le obj obj_val =
  match obj with
  | (x, _) -> Sol.ivar_le x obj_val


let probe_objective print_model solver model obj =
  (* Compute bounds *)
  match !Opts.obj_probe_limit with
  | None -> model (* Don't probe *)
  | Some probe_lim ->
    (* Set up limits for probe steps. *)
    let limits =
      let l = !Opts.limits in
      if l.Sol.max_conflicts > 0 then
        (fun () ->
          let rlim = relative_limits solver l in
          { rlim with
              Sol.max_conflicts = min probe_lim (rlim.Sol.max_conflicts) })
      else
        (fun () -> { (relative_limits solver l)
                     with Sol.max_conflicts = probe_lim })
    in
    (* Do some probing *)
    let rec aux model lb ub step =
      if lb = ub then
        model
      else begin
        let mid = max lb (ub - step) in
        if not (Sol.assume solver (obj_le obj mid)) then
          (Sol.retract solver ; model)
        else
          match Sol.solve solver (limits ()) with
          | Sol.SAT ->
            let m' = Sol.get_model solver in 
            let _ = print_model m' in
            (* let ub' = Sol.int_value m' obj in *)
            let ub' = eval_obj m' obj in
            (Sol.retract solver ; aux m' lb ub' (2*step))
          | Sol.UNSAT ->
            (Sol.retract solver ; aux model (mid+1) ub 1)
          | Sol.UNKNOWN -> (Sol.retract solver; model)
      end
    in
    aux model (Sol.ivar_lb (fst obj)) (eval_obj model obj) 1
      
let solve_minimize overall_limits print_model print_nogood solver obj assumps =
  assert (List.length assumps = 0) ;
  let fmt = Format.std_formatter in
  let limits =
    (fun () -> relative_limits solver overall_limits) in
  let print_each =
    if !Opts.max_solutions < 1 then
      fun m -> print_model Format.std_formatter m
    else
      fun m -> ()
  in
  let rec aux model =
    let obj_val = eval_obj model obj in
    (* let _ = Format.fprintf Format.err_formatter "%% z = %d, f(xs) = %d@." (Sol.int_value model (fst obj)) obj_val in *)
    (* let _ = Format.fprintf fmt "%% Candidate: %d, %d@." obj_val (Sol.int_value model (fst obj)) in *)
    if not (Sol.post_atom solver (obj_lt obj obj_val)) then
      (begin
        if !Opts.max_solutions > 0 then
          print_model fmt model
       end ;
       Format.fprintf fmt "==========@." ;
       model)
    else
      match Sol.solve solver (limits ()) with
      | Sol.UNKNOWN ->
         (begin
            if !Opts.max_solutions > 0 then
              print_model fmt model
            end ;
          Format.fprintf fmt "%%%% INCOMPLETE@." ;
          model)
      | Sol.UNSAT ->
         ((* print_model fmt model ; *)
          begin
            if !Opts.max_solutions > 0 then
              print_model fmt model
            end ;
          Format.fprintf fmt "==========@." ;
          model)
      | Sol.SAT ->
        (* )
        aux (Sol.get_model solver)
        ( *)
        let m = Sol.get_model solver in
        let _ = print_each m in
        let m' = probe_objective print_each solver m obj in
        aux m'
        (* *)
  in
  match Sol.solve solver (limits ()) with
  | Sol.UNKNOWN -> (Format.fprintf fmt "=====UNKNOWN=====@." ; None)
  | Sol.UNSAT ->
    (* Format.fprintf fmt "UNSAT@." *)
    (Format.fprintf fmt "=====UNSATISFIABLE=====@." ; None)
  | Sol.SAT ->
    (* Some (aux (Sol.get_model solver)) *)
    let m = Sol.get_model solver in
    let _ = print_each m in
    Some (aux (probe_objective print_each solver (Sol.get_model solver) obj))

type ovar_state = {
  coeff : int ;
  lb : int ;
  residual : int ;
}
let as_ovar_state coeff lb = { coeff = coeff ; lb = lb ; residual = coeff }

let init_thresholds solver obj =
  let thresholds = H.create 17 in
  let min = ref 0 in
  List.iter (fun (c, x) -> 
    let l = Sol.ivar_lb x in
    min := !min + c * l ;
    H.add thresholds x { coeff = c ; lb = l ; residual = c ; }
  ) obj ;
  !min, thresholds

let adjust_ovar_state st k = 
  assert (k <= st.residual) ;
  if k < st.residual then
    { st with residual = st.residual - k }
  else
    { coeff = st.coeff ;
      lb = st.lb+1 ;
      residual = st.coeff; }

let update_thresholds_factor thresholds bounds =
  (* let diff = ref max_int in *)
  let delta = Array.fold_left (fun d (x, b) ->
    let st = H.find thresholds x in
    assert (b > st.lb) ;
    (* diff := min (b - st.lb) !diff ; *)
    min d st.residual) max_int bounds in
  (*
  let _ = if !diff > 1 then
    Format.fprintf Format.err_formatter "%% bound improvement: %d@." !diff
  in
  *)
  let atoms = Array.map (fun (x, _) ->
    let st = H.find thresholds x in
    let at = Sol.ivar_gt x st.lb in
    let st' = adjust_ovar_state st delta in
    if st'.lb = Sol.ivar_ub x then
      H.remove thresholds x
    else
      H.replace thresholds x st' ;
    (1, at)) bounds in
  1, delta, atoms

(* Look at the residuals to decide whether to factor or 
 * split. *)
let update_thresholds_adapt thresholds bounds =
  (* let diff = ref max_int in *)
  let coeffs = Array.map
    (fun (x, _) -> let st = H.find thresholds x in st.residual) bounds in
  let min_coeff = Util.array_fold1 min coeffs in
  let factor_bound = Array.fold_left (fun s d -> if d < (2 * min_coeff) then max s d else s) min_coeff coeffs in
  let keep_var_coeff = (min_coeff <> factor_bound) in
  let _ = if keep_var_coeff && !Opts.verbosity > 3 then
    Format.fprintf Format.err_formatter "%% Keeping coeffs in range: [%d, %d].@." min_coeff factor_bound in
  let lb, coeff = if keep_var_coeff then min_coeff, 1 else 1, min_coeff in
  let atoms = Array.map (fun (x, _) ->
    let st = H.find thresholds x in
    let at = Sol.ivar_gt x st.lb in
    let x_delta = if st.residual < factor_bound then st.residual else factor_bound in
    let var_coeff = if keep_var_coeff then x_delta else 1 in
    let st' = adjust_ovar_state st x_delta in
    if st'.lb = Sol.ivar_ub x then
      H.remove thresholds x
    else
      H.replace thresholds x st' ;
    (var_coeff, at)) bounds in
  lb, coeff, atoms

let update_thresholds thresholds bounds =
  if !Opts.core_factor_coeff then
    update_thresholds_factor thresholds bounds
  else
    update_thresholds_adapt thresholds bounds

let log_thresholds thresholds =
  let fmt = Format.err_formatter in
  Format.fprintf fmt "{|@[<hov 2>[P:coeff,lb,res]" ;
  Hashtbl.fold (fun k st tl -> (k, st) :: tl) thresholds [] |> List.sort compare |>
    List.iter (fun (k, st) ->
  (* Hashtbl.iter (fun k st -> *) Format.fprintf fmt "@ [%d:%d,%d,%d]"
    (Sol.ivar_pred k |> Int32.to_int) st.coeff st.lb st.residual) (* thresholds *) ;
  Format.fprintf fmt "@ |}@]@."

let post_thresholds solver thresholds =
  (* H.fold (fun x t r -> r && Sol.assume solver (Sol.ivar_le x t.lb)) thresholds true *)
  H.fold (fun x t r ->
    if r then
      Sol.assume solver (Sol.ivar_le x t.lb)
    else false) thresholds true

let post_thresholds_list solver thresholds =
  L.fold_left (fun r (x, t) ->
    if r then
      Sol.assume solver (Sol.ivar_le x t.lb)
    else false) true thresholds

let post_thresholds_upto solver thresholds min_coeff =
  H.fold (fun x st r ->
    if r then
      if st.coeff >= min_coeff then
        (Sol.assume solver (Sol.ivar_le x st.lb))
      else
        true
    else
      false) thresholds true

let rec post_thresholds_subset solver thresholds vars =
  match vars with
  | [] -> true
  | x :: xs ->
    let st = H.find thresholds x in
    if Sol.assume solver (Sol.ivar_le x st.lb) then
      post_thresholds_subset solver thresholds xs
    else
      false

let build_pred_map solver vars =
  let map = H.create 17 in
  List.iter (fun (_, x) ->
    try
      let _ = H.find map (Sol.ivar_pred x) in
      failwith "Pred already exists."
    with Not_found -> 
      try
        let _ = H.find map (Sol.ivar_pred (Sol.intvar_neg x)) in
        failwith "Pred already exists in negated form."
      with Not_found ->
        H.add map (Sol.ivar_pred x) x) vars ;
  map

let lb_of_atom pred_map at =
  (* Find the var corresponding to the atom. *)
  let pred = at.At.pid in
  let x = H.find pred_map pred in
  let at0 = Sol.ivar_ge x 0 in
  assert (at0.At.pid = pred) ;
  let delta = Int64.sub at.At.value at0.At.value in
  (x, Int64.to_int delta)
  
let check_core solver core =
  let res =
    if apply_assumps solver (Array.map At.neg core |> Array.to_list) then
      Sol.solve solver (Sol.unlimited ())
    else
      Sol.UNSAT
  in
  assert (res = Sol.UNSAT) ;
  Sol.retract_all solver
  
let post_bool_sum_geq_ solver r bs k =
  let xs = Array.map (fun b ->
    let x = Sol.new_intvar solver 0 1 in
    let at = Sol.ivar_ge x 1 in
    let _ = Sol.post_clause solver [|b ; At.neg at|] in
    let _ = Sol.post_clause solver [|At.neg b ; at|] in
    1, x) bs in
  B.linear_le solver At.at_True (Array.append [|-1, r|] xs) (-k)

let post_bool_sum_geq solver r bs k : bool =
  B.bool_linear_ge solver (At.at_True) r (Array.map (fun b -> 1, b) bs) k
  
let process_core solver pred_map thresholds core =
  (* check_core solver core ; *)
  if Array.length core = 1 then
    (* let _ = Format.fprintf Format.err_formatter "%% singleton@." in *)
    let (x, b) = lb_of_atom pred_map core.(0) in
    let st = H.find thresholds x in
    assert(b > st.lb) ;
    let cost = st.residual + st.coeff * (b - st.lb - 1) in
    let _ = H.replace thresholds x { coeff = st.coeff ; lb = b ; residual = st.coeff } in
    let okay = Sol.post_atom solver core.(0) in
    assert okay ;
    cost
  else
    begin
      (* Relate penalty to core *)
      (* Now update thresholds *)
      let bounds = Array.map (lb_of_atom pred_map) core in    
      (*
      let _ = Util.print_array ~pre:"%% @[[" ~post:"]@]@." ~sep:",@ " 
        (fun fmt (x, b) -> Format.fprintf fmt "x%d >= %d" (Sol.ivar_pred x |> Int32.to_int) b) Format.err_formatter bounds in
        *)
      let lb, coeff, atoms = update_thresholds thresholds bounds in
      (* Create penalty var *)
      let p = Sol.new_intvar solver lb (Array.length core) in
      (* let _ = post_bool_sum_geq solver p atoms (-1) in *)
      let _ = B.bool_linear_ge solver (At.at_True) p atoms 0 in
      let _ = Sol.post_clause solver core in
      (* Format.fprintf Format.err_formatter "%% Adding penalty var: x%d with coefficient %d.@."
        (Sol.ivar_pred p |> Int32.to_int) delta ; *)
      H.add pred_map (Sol.ivar_pred p) p ;
      H.add thresholds p { coeff = coeff ; lb = lb ; residual = coeff ; } ;
      (* ) log_thresholds thresholds ; ( *)
      lb * coeff
    end

let trim_core solver pred_map thresholds core =
  if Array.length core = 1 then
    let _ = if !Opts.verbosity > 3 then Format.fprintf Format.err_formatter "%% singleton@." in
    let (x, b) = lb_of_atom pred_map core.(0) in
    let st = H.find thresholds x in
    assert(b > st.lb) ;
    let cost = st.residual + st.coeff * (b - st.lb - 1) in
    let _ = H.replace thresholds x { coeff = st.coeff ; lb = b ; residual = st.coeff } in
    (* let okay = Sol.post_atom solver core.(0) in 
    assert okay ; *)
    cost, 1, [| 1, core.(0) |]
  else
    let bounds = Array.map (lb_of_atom pred_map) core in
    let lb, coeff, atoms = update_thresholds thresholds bounds in
    (* let _ = Sol.post_clause solver core in *)
    lb, coeff, atoms

let apply_cores print_penalty solver pred_map thresholds deferred_cores =
  List.iter (fun (low, coeff, c) ->
    if Array.length c > 1 then
      begin
        (* let low = Util.array_fold1 (min) (Array.map fst c) in *)
        let high = Util.array_fold1 (+) (Array.map fst c) in
        let p = Sol.new_intvar solver low high in
        print_penalty Format.err_formatter p c ;
        let _ = B.bool_linear_ge solver (At.at_True) p c 0 in
        H.add pred_map (Sol.ivar_pred p) p ;
        H.add thresholds p { coeff = coeff ; lb = low; residual = coeff; }
      end
    ) deferred_cores

let core_excess m core =
  let (lb, coeff, c) = core in
  let cost = Array.fold_left
    (fun s (c, at) -> s + c * (if Sol.atom_value m at then 1 else 0)) 0 c in
  cost - lb

(*
let core_violations m core =
  let (lb, delta, c) = core in
  Array.fold_left (fun s (_, at) -> s + if Sol.atom_value m at then 1 else 0) 0 c
  *)

(* What is the violation from these cores not yet priced into the lower bound? *)
(*
let core_excess m core =
  let (lb, coeff, c) = core in
  let vio = core_violations m core in
  (* assert (vio > 0) ; *)
  coeff * vio - lb
  *)

let cores_excess m cores = List.fold_left (fun e c -> e + core_excess m c) 0 cores

let core_coeff (_, c, _) = c
let core_cost (lb, _, _) = lb

(* FIXME *)
let core_violation_score mode m =
  match mode with
  | Opts.Uniform -> (fun c -> if core_excess m c > 0 then 1 else 0)
  | Opts.Violation -> (fun c -> core_excess m c)
  | Opts.Weight -> (fun c -> if core_excess m c > 0 then (core_coeff c) else 0)
  | Opts.WeightViolation -> (fun c -> (core_coeff c) * (core_excess m c))

(* Collect only the set of cores with maximum violation. *)
let split_cores m cores =
  let score_core = core_violation_score !Opts.core_selection m in
  (* let _ = Format.fprintf Format.err_formatter "%% Pending: %d@." (List.length cores) in *)
  let _ = if !Opts.verbosity > 3 then
    Util.print_list ~post:"@]]@." Format.pp_print_int Format.err_formatter (List.map (fun c -> core_excess m c) cores) in
  let rec aux cost vio_cores def_cores pending =
    match pending with
    | [] -> (cost, vio_cores, def_cores)
    | (core :: rest) ->
      let c = score_core core in
      if c < cost then
        aux cost vio_cores (core :: def_cores) rest
      else if c > cost then
        aux c [core] (List.rev_append vio_cores def_cores) rest
      else
        aux c (core :: vio_cores) def_cores rest
  in
  let _, vio, rest = aux 1 [] [] cores in
  (* assert (List.length vio + List.length rest = List.length cores) ; *)
  match !Opts.core_reformulation, vio with
  | Opts.ReformOne, (hd :: vio') ->
    [hd], List.rev_append vio' rest 
  | Opts.ReformEager, vio -> List.rev_append vio rest, []
  | _, _ -> vio, rest
    
let log_core_iter =
  let iters = ref 0 in
  (fun lb ->
    incr iters ;
    Format.fprintf Format.err_formatter "%% Unsat core iteration: %d (lb %d).@." !iters lb)

let try_thresholds solver thresholds =
  if post_thresholds solver thresholds then
    let limits = relative_limits solver !Opts.limits in
    Sol.solve solver limits
  else
    Sol.UNSAT

let try_thresholds_list solver thresholds = 
  if post_thresholds_list solver thresholds then
    let limits = relative_limits solver !Opts.limits in
    Sol.solve solver limits
  else
    Sol.UNSAT

let time_is_exceeded solver limits =
  let s = Sol.get_statistics solver in
  (* let _ = Format.fprintf Format.err_formatter "%% time: %f, max %f@." s.Sol.time limits.Sol.max_time in *)
  limits.Sol.max_time > 0. && s.Sol.time > limits.Sol.max_time

let try_thresholds_upto solver thresholds min_coeff limits =
  if time_is_exceeded solver limits then
    Sol.UNKNOWN
  else if post_thresholds_upto solver thresholds min_coeff then
    (* let limits = relative_limits solver !Opts.limits in *)
    Sol.solve solver (relative_limits solver limits)
  else
    Sol.UNSAT

let try_thresholds_subset solver thresholds vars =
  if post_thresholds_subset solver thresholds vars then
    let limits = relative_limits solver !Opts.limits in
    Sol.solve solver limits
  else
    Sol.UNSAT

let rec solve_core' print_nogood solver pred_map thresholds lb =
  log_core_iter lb ;
  (* let okay = post_thresholds solver thresholds in
  let limits = relative_limits solver !Opts.limits in
  match Sol.solve solver limits with *)
  match try_thresholds solver thresholds with
  | Sol.SAT ->
    begin
      let m = Sol.get_model solver in
      Sol.retract_all solver ;
      (* H.iter (fun x st -> assert (Sol.int_value m x <= st.lb)) thresholds ; *)
      (* Check the objective *)
      Some m
    end
  | Sol.UNSAT -> 
    let core = Sol.get_conflict solver in
    begin
      (* print_nogood Format.err_formatter core ;  *)
      Sol.retract_all solver ;
      assert (Array.length core > 0) ;
      let delta = process_core solver pred_map thresholds core in
      solve_core' print_nogood solver pred_map thresholds (lb + delta)
    end
  | Sol.UNKNOWN ->
    begin
      Sol.retract_all solver ;
      None
    end

(* Stratified version of unsat-core based optimization *)
let next_coeff thresholds coeff =
  H.fold (fun x st c ->
    if st.coeff >= coeff then
      c
    else
      max c st.coeff) thresholds 0

type core_result = 
  | Sat of (Sol.model * int * (Sol.intvar, ovar_state) H.t)
  | Opt of Sol.model
  | Unsat
  | Unknown

let tighten_objective_bounds solver thresholds gap =
  let killed = ref [] in
  let okay = H.fold (fun x st r ->
    r &&
    if gap < st.residual then
      let _ = if !Opts.verbosity > 1 then Format.fprintf Format.err_formatter "%% Fixed var x%d to %d (gap %d, residual %d).@."
        (Sol.ivar_pred x |> Int32.to_int) st.lb gap st.residual in
      killed := x :: !killed ;
      Sol.post_atom solver (Sol.ivar_le x st.lb)
    else
      if gap < st.residual + st.coeff * ((Sol.ivar_ub x) - st.lb - 1) then
        let ub' = st.lb + 1 + (gap - st.residual) / st.coeff in
        let _ = if !Opts.verbosity > 1 then Format.fprintf Format.err_formatter "%% Tightened var x%d from %d to %d.@."
          (Sol.ivar_pred x |> Int32.to_int) (Sol.ivar_ub x) ub' in
        Sol.post_atom solver (Sol.ivar_le x (st.lb + 1 + ((gap - st.residual) / st.coeff)))
      else
        true) thresholds true in
    List.iter (H.remove thresholds) !killed ;
    okay

let rec solve_core_strat print_model print_nogood print_penalty solver obj incumbent pred_map thresholds min_coeff deferred_cores lb limits =
  let _ = if !Opts.verbosity > 0 then
    (log_core_iter lb ;
    Format.fprintf Format.err_formatter "%% Min coeff: %d, incumbent value %d@." min_coeff (Solver.int_value incumbent obj))
  in
  if Sol.int_value incumbent obj = lb then
    let _ = if !Opts.verbosity > 1 then
       Format.fprintf Format.err_formatter "%% Un-reformulated cores: %d@." (List.length deferred_cores) in
    Opt incumbent
  else
  begin
  begin
    if !Opts.core_harden then
      let gap = (Solver.int_value incumbent obj) - lb in
      let okay = tighten_objective_bounds solver thresholds gap in
      assert okay
  end ;
  (* We know there exists a minimum-weight model for [obj.(0), ..., obj.(idx-1)].
   * Now expand to the rest of the variables. *)
  match try_thresholds_upto solver thresholds min_coeff limits with
  | Sol.SAT ->
    begin
      (* Format.fprintf Format.err_formatter "%% [SAT].@." ; *)
      let m = Sol.get_model solver in
      (* let _ = print_model Format.std_formatter m in *)
      (* )
      let fmt = Format.err_formatter in
      Format.fprintf fmt "{|@[<hov 2>" ;
      Hashtbl.fold (fun x st tl -> (x, st) :: tl) thresholds [] |> List.sort compare
        |> List.iter (fun (x, st) -> Format.fprintf fmt "@ [%d:%d|%d]"
        (Sol.ivar_pred x |> Int32.to_int) st.lb (Sol.int_value m x)) ;
      Format.fprintf fmt "@ |}@]@." ;
      ( *)
      Sol.retract_all solver ;
      let m' = if (Sol.int_value m obj) < (Sol.int_value incumbent obj) then
        (* let _ = Format.fprintf Format.std_formatter "%% [%d -> %d]@." (Sol.int_value incumbent obj) (Sol.int_value m obj) in *)
        let _ = print_model Format.std_formatter m in
        m
        else incumbent in
      match split_cores m deferred_cores with
      (* match deferred_cores, [] with *)
      | [], rest ->
        (* No cores have more than one violation. Continue with lower objectives *)
        begin
          let _ = if !Opts.verbosity > 1 then
            Format.fprintf Format.err_formatter "%% Un-reformulated cores: %d@." (List.length rest) in
          let coeff' = next_coeff thresholds min_coeff in
          if coeff' = 0 then
            let _ = if !Opts.verbosity > 1 then log_thresholds thresholds in
            (* let _ = Format.fprintf Format.err_formatter "%% objective %d@." (Sol.int_value m obj) in *)
            (* Check the un-reformulated cores. *)
            (*
            let solve_with s c =
              let r = apply_assumps s (Array.to_list c) && Sol.solve s (Sol.unlimited ()) = Sol.SAT in
              Sol.retract_all s ;
              r in
            let _ = List.iter (fun c -> assert (not (solve_with solver (Array.map At.neg (snd c))))) rest in
            *)
            Opt m'
          else
            solve_core_strat print_model print_nogood print_penalty solver obj m' pred_map thresholds coeff' rest lb limits
        end
      | vio_cores, other_cores ->
        begin
          apply_cores print_penalty solver pred_map thresholds vio_cores ;
          solve_core_strat print_model print_nogood print_penalty solver obj m' pred_map thresholds min_coeff other_cores lb limits 
        end
    end
  | Sol.UNSAT -> 
    let core = Sol.get_conflict solver in
    begin
      let _ = if !Opts.verbosity > 2 then
        print_nogood Format.err_formatter core in
      Sol.retract_all solver ;
      assert (Array.length core > 0) ;
      if Array.length core = 0 then
        Opt incumbent
      else
        if not (Sol.post_clause solver core) then
          Opt incumbent
        else
          let clb, coeff, core = trim_core solver pred_map thresholds core in
          (* let _ = print_nogood Format.err_formatter core in *)
          solve_core_strat print_model print_nogood print_penalty solver obj incumbent pred_map thresholds min_coeff ((clb, coeff, core) :: deferred_cores) (lb + coeff * clb) limits
    end
  | Sol.UNKNOWN ->
    begin
      Sol.retract_all solver ;
      apply_cores print_penalty solver pred_map thresholds deferred_cores ;
      Sat (incumbent, lb, thresholds)
    end
  end

let solve_with_assumption solver at limits =
  if not (Sol.assume solver at) then
    Sol.UNSAT
  else if time_is_exceeded solver limits then
    Sol.UNKNOWN
  else
    Sol.solve solver limits


let solve_with_assumptions solver assumps limits =
  let rec aux assumps =
    match assumps with
    | [] ->
      Sol.solve solver limits
    | at :: assumps' ->
      if not (Sol.assume solver at) then
        Sol.UNSAT
      else if time_is_exceeded solver limits then
        Sol.UNKNOWN
      else
        aux assumps'
  in
  let r = aux assumps in
  let _ = Sol.retract_all solver in
  r

let shrink_core solver core step_limit =
  let rec aux pending acc =
    match pending with
      | [] -> List.rev acc |> List.map At.neg |> Array.of_list
      | at :: rest ->
        begin
          match solve_with_assumptions solver (List.rev_append acc rest) step_limit with
          | Sol.UNSAT -> aux rest acc
          | _ -> aux rest (at :: acc)
        end
  in
  aux (Array.to_list core |> List.map At.neg) []


 (* Alternate reinterpretation of core-guided optimisation for integers.
 * Instead of carving off slices of int-vars, it just groups subterms.
 *)
module IntCore : sig
  type state

  type configuration = {
    print_model : Sol.model -> unit ;
    print_nogood : At.t array -> unit ;
    ivar_name : Sol.intvar -> string ;
    limits : Sol.limits ;
  }

  val init_state : Sol.intvar -> (int * Sol.intvar) array -> int -> Sol.model -> state
  val solve : configuration -> Sol.solver -> state -> core_result
end = struct
  type oterm = {
    coeff : int ;
    lb : int ;
  }
  type otable = (Sol.intvar, oterm) H.t
  type delayed_core = oterm * ((int * Sol.intvar) list)

  type configuration = {
    print_model : Sol.model -> unit ;
    print_nogood : At.t array -> unit ;
    ivar_name : Sol.intvar -> string ;
    limits : Sol.limits ;
  }

  type result =
    | SAT of Sol.model
    | UNSAT of At.t array
    | UNKNOWN

  type state = {
    obj : Sol.intvar ;

    thresholds : otable ;
    pred_map : (Int32.t, Sol.intvar) H.t ;

    mutable pending : delayed_core list ;
    mutable min_coeff : int ;
    mutable obj_lb : int ;
    mutable obj_ub : int ;
    mutable incumbent : Sol.model ;
  }

  let init_state obj terms cst incumbent =
    let thresholds = H.create 17 in
    let pred_map = H.create 17 in
    let min_coeff = ref 0 in
    let lb = Array.fold_left (fun s (k, x) ->
      assert (k > 0);
      let x_lb = Sol.ivar_lb x in
      let st = { coeff = k ; lb = x_lb } in
      H.add thresholds x st ;
      H.add pred_map (Sol.ivar_pred x) x ;
      min_coeff := max k !min_coeff ;
      s + (k * x_lb)) 0 terms in
    {
      obj = obj ;
      thresholds = thresholds ;
      pred_map = pred_map ;

      pending = [] ;
      min_coeff = !min_coeff ;
      obj_lb = lb + cst ;
      obj_ub = Sol.int_value incumbent obj ;
      incumbent = incumbent ;
    }

  let tighten_bounds solver state =
    let gap = state.obj_ub - state.obj_lb in
    (* let _ = Format.fprintf Format.err_formatter "%% lb: %d, ub: %d, gap: %d@." state.obj_lb state.obj_ub gap in *)
    H.fold (fun x st r ->
      r &&
      let x_ub = st.lb + (gap / st.coeff) in
      if x_ub < (Sol.ivar_ub x) then
        (* let _ = Format.fprintf Format.err_formatter "%% [var lb: %d, st.lb: %d, ub: %d, new_ub: %d@."
          (Sol.ivar_lb x) st.lb (Sol.ivar_ub x) x_ub in *)
        Sol.post_atom solver (Sol.ivar_le x x_ub)
      else true) state.thresholds true

  let update_incumbent (config : configuration) solver state m =
    let m_obj = Sol.int_value m state.obj in
    (* let _ = Format.fprintf Format.err_formatter "%% model value: %d@." m_obj in *)
    assert (m_obj >= state.obj_lb) ;
    let _ =
      if m_obj < state.obj_ub then
        begin
          state.incumbent <- m ;
          state.obj_ub <- m_obj ;
          (* TODO Print the model *)
          config.print_model m ;
          if !Opts.core_harden then
            let okay = tighten_bounds solver state in
            assert okay
        end
    in
    ()

  (* Factor out a core from the current set of penalties. *)
  let factor_core state core =
    let min_coeff = ref max_int in
    let min_delta = ref max_int in
    let s, xs = Array.fold_left (fun (s, xs) at ->
        let (x, b) = lb_of_atom state.pred_map at in
        let st = H.find state.thresholds x in
        min_delta := min (b - st.lb) !min_delta ;
        min_coeff := min st.coeff !min_coeff ;
        s + st.lb, (1, x) :: xs) (0, []) core in
    (* Format.fprintf Format.err_formatter "%% [%d | %d]@." !min_coeff !min_delta ; *)
    state.obj_lb <- state.obj_lb + !min_coeff * !min_delta ;
    begin
      List.iter (fun (_, x) ->
          let st = H.find state.thresholds x in
          if st.coeff = !min_coeff then
            H.remove state.thresholds x
          else
            H.replace state.thresholds x { st with coeff = st.coeff - !min_coeff }
        ) xs ;
      let d_core = { lb = s + !min_delta ; coeff = !min_coeff }, xs in
      state.pending <- d_core :: state.pending
    end
  
  (* Instead of taking the min coeff, we need the gcd. *)
  let isolate_core state core =
    (* let max_coeff = ref 0 in *)
    let s, min_delta, xs_pre = Array.fold_left (fun (s, min_delta, xs) at ->
        let (x, b) = lb_of_atom state.pred_map at in
        let st = H.find state.thresholds x in
        H.remove state.thresholds x ;
        (* max_coeff := max st.coeff !max_coeff ; *)
        let min_delta' = min (st.coeff * (b - st.lb)) min_delta in
        s + st.coeff * st.lb, min_delta', (st.coeff, x) :: xs) (0, max_int, []) core in
    let gcd_coeff = Util.gcd_list (List.map fst xs_pre) in
    (* Format.fprintf Format.err_formatter "%% gcd: %d, max: %d@." gcd_coeff !max_coeff ; *)
    let xs = List.map (fun (c, x) -> c / gcd_coeff, x) xs_pre in
    (* Format.fprintf Format.err_formatter "%% [%d | %d]@." !min_coeff !min_delta ; *)
    state.obj_lb <- state.obj_lb + min_delta ;
    let d_core = { lb = (s + min_delta) / gcd_coeff ; coeff = gcd_coeff }, xs in
    state.pending <- d_core :: state.pending

  (* Use the domain and coefficients to decide whether to factor or isolate. *)
  let factor_or_isolate_core state core =
    (* let max_coeff = ref 0 in *)
    let min_delta, xs_pre = Array.fold_left (fun (min_delta, xs) at ->
        let (x, b) = lb_of_atom state.pred_map at in
        let st = H.find state.thresholds x in
        (* H.remove state.thresholds x ; *)
        (* max_coeff := max st.coeff !max_coeff ; *)
        let delta = (b - st.lb) in
        let min_delta' = min (st.coeff * delta) min_delta in
        min_delta', (st.coeff, delta, x) :: xs) (max_int, []) core in
    let unfactor_max, unfactor_coeffs = List.map (fun (c, _, _) -> c) xs_pre |> List.fold_left (fun (s, cs) c ->
      if c > 2 * min_delta then s, cs else max s c, c::cs) (1, []) in
    (* let _ = Format.fprintf Format.err_formatter "%% Min delta: %d, unfactor_coeff: %d@." min_delta unfactor_max in *)
    let gcd_coeff = List.fold_left Util.gcd unfactor_max unfactor_coeffs in
    (* Format.fprintf Format.err_formatter "%% gcd: %d, max: %d@." gcd_coeff !gcd_coeff ; *)
    (* *)
    let s = ref 0 in
    let dmin = ref max_int in
    let xs = List.map (fun (c, d, x) ->
      let st = H.find state.thresholds x in
      let c' = 
        if c > unfactor_max then
          let _ = H.replace state.thresholds x { lb = st.lb ; coeff = st.coeff - unfactor_max } in
          unfactor_max
        else
          let _ = H.remove state.thresholds x in
          c
      in
      s := !s + c' * st.lb ;
      dmin := min !dmin (c' * d) ;
      (c' / gcd_coeff, x)
     ) xs_pre in
    (* Format.fprintf Format.err_formatter "%% [%d | %d]@." !min_coeff !min_delta ; *)
    state.obj_lb <- state.obj_lb + !dmin ;
    let d_core = { lb = (!s + !dmin)/gcd_coeff ; coeff = gcd_coeff }, xs in
    state.pending <- d_core :: state.pending

  (* Search for a solution to the current subproblem *)
  let try_state solver state limits =
    let okay = H.fold (fun x st r ->
                   r &&
                     if st.coeff >= state.min_coeff then
                       (Sol.assume solver (Sol.ivar_le x st.lb))
                     else
                       true) state.thresholds true in
    let result =
      if time_is_exceeded solver limits then
        UNKNOWN
      else if (not okay) then
        UNSAT (Sol.get_conflict solver)
      else
        match Sol.solve solver (relative_limits solver limits) with
        | Sol.SAT -> SAT (Sol.get_model solver)
        | Sol.UNSAT -> UNSAT (Sol.get_conflict solver)
        | Sol.UNKNOWN -> UNKNOWN
    in
    Sol.retract_all solver ;
    result

  let probe_lb solver state x b =
  match !Opts.obj_probe_limit with
  | None -> b (* Don't probe *)
  | Some probe_lim ->
    (* Set up limits for probe steps. *)
    let limits =
      let l = !Opts.limits in
      if l.Sol.max_conflicts > 0 then
        (fun () ->
          let rlim = relative_limits solver l in
          { rlim with
              Sol.max_conflicts = min probe_lim (rlim.Sol.max_conflicts) })
      else
        (fun () -> { (relative_limits solver l)
                     with Sol.max_conflicts = probe_lim })
    in
    let ub = Sol.ivar_ub x in
    let rec aux lb step =
      (* Format.fprintf Format.err_formatter "%% Probe step: %d@." step ;  *)
      if lb > ub then
        lb
      else
        let _ = Sol.retract_all solver in
        let lb' = min ub (lb + step) in
        match solve_with_assumption solver (Sol.ivar_le x lb') (limits ()) with
        | Sol.UNSAT ->
          begin
            let core = Sol.get_conflict solver in
            assert (Array.length core <= 1) ;
            if Array.length core = 0 then
              ub+1
            else
              let (_, lb'') = lb_of_atom state.pred_map core.(0) in
              aux lb'' (1 + 2 * step)
          end
        | Sol.SAT | Sol.UNKNOWN -> lb
      in
      let b' = aux b 0 in
      Sol.retract_all solver ;
      b'

  (* Introduce the penalty term for a delayed core. *)
  let print_penalty config x vars =
    if !Opts.verbosity > 2 then
      begin
        Format.fprintf Format.err_formatter
          "%% VAR: %s = " (config.ivar_name x) ;
        Util.print_list Format.pp_print_string ~pre:"" ~post:"@." ~sep:"+" Format.err_formatter (List.map (fun (c, x) -> Format.sprintf "%d %s" c (config.ivar_name x)) vars)
      end

  let apply_core config solver state (term, ts) =
    match ts with
    | [(c, x)] ->
      begin
        let lb' = probe_lb solver state x term.lb in
        state.obj_lb <- state.obj_lb + c * term.coeff * (lb' - term.lb) ;
        H.add state.thresholds x { lb = lb' ; coeff = term.coeff * c }
      end
    | _ ->
      begin
        let lb = term.lb in
        let ub = lb + (state.obj_ub - state.obj_lb) / term.coeff in
        (* let ts = List.map (fun x -> 1, x) vars |> Array.of_list in *)
        (* Create the new penalty term *)
        let p = Sol.new_intvar solver lb ub in
        let _ = print_penalty config p ts in
        (*
        let _ = if !Opts.verbosity > 3 && term.coeff > 1 then
          Format.fprintf Format.err_formatter "%% COEFF: %d@." term.coeff in
          *)
        let _ = B.linear_le solver At.at_True (Array.of_list ((-1, p) :: ts)) 0 in
        H.add state.pred_map (Sol.ivar_pred p) p ;
        (* ) H.add state.thresholds p term ; ( *)
        let lb' = probe_lb solver state p term.lb in
        state.obj_lb <- state.obj_lb + term.coeff * (lb' - term.lb) ;
        H.add state.thresholds p { lb = lb' ; coeff = term.coeff }
        (* *)
      end
    
  let decrease_coeff state =
    let new_coeff = ref 1 in
    H.iter (fun x st ->
        if st.coeff < state.min_coeff then
          new_coeff := max st.coeff !new_coeff) state.thresholds ;
    state.min_coeff <- !new_coeff ;
    ()
    
  let core_violation m (term, vars) =
    let cost = List.fold_left (fun d (c, x) -> d + c * (Sol.int_value m x)) 0 vars in
    cost - term.lb

  let split_cores state m =
    let vio, rest = List.fold_left (fun (vio, rest) core ->
      if core_violation m core > 0 then
        core :: vio, rest
      else
        vio, core :: rest) ([], []) state.pending in
    state.pending <- rest ;
    vio


  let rec solve config solver state =
    (* Format.fprintf Format.err_formatter "%% [%d | %d].@." state.obj_lb state.obj_ub ; *)
    assert (state.obj_lb <= state.obj_ub) ;
    if state.obj_lb = state.obj_ub then
      Opt state.incumbent
    else
      match try_state solver state config.limits (* (relative_limits solver config.limits) *) with
      | SAT m ->
         begin
           let _ = if !Opts.verbosity > 3 then
             Format.fprintf Format.err_formatter "%% Found model.@." in
           update_incumbent config solver state m ;
           let _ = match split_cores state m with
             (* No over-violated cores *)
            | [] -> decrease_coeff state
            | vio_cores -> List.iter (apply_core config solver state) vio_cores
           in
           solve config solver state
         end
      | UNSAT core_ ->
         begin
           let core = shrink_core solver core_ { (Sol.unlimited ()) with Sol.max_conflicts = 50 } in 
           (* let core = core_ in *)
           if Array.length core > 0 then
             begin
              let core' =
              (*
                if Array.length core = 1 then
                  let (x, b) = lb_of_atom state.pred_map core.(0) in
                  let b' = probe_lb solver state x b in
                  [| Sol.ivar_ge x b' |]
                else
                  *)
                  core in
              let _ =
                if !Opts.core_factor_coeff then
                  factor_core state core'
                else
                  (* isolate_core state core' *)
                  factor_or_isolate_core state core'
              in
              let _ = if !Opts.verbosity > 1 then
                Format.fprintf Format.err_formatter "%%%% Found core of size %d, new lb: %d@." (Array.length core) state.obj_lb ;
                if !Opts.verbosity > 2 then
                  config.print_nogood core'
              in
              solve config solver state
             end
           else
             Opt state.incumbent
         end
      | UNKNOWN ->
         let ovars = H.create 17 in
         let _ = H.iter (fun x st -> H.add ovars x (as_ovar_state st.coeff st.lb)) state.thresholds in
         List.iter (apply_core config solver state) state.pending ;
         Sat (state.incumbent, state.obj_lb, ovars)
end


  (*
let solve_core print_model print_nogood solver obj_var obj k =
  (* Post penalty thresholds *)
  let limits () = relative_limits solver !Opts.limits in
  match Sol.solve solver (limits ()) with
  | Sol.SAT ->
    (* Found a first model. *)
    let m = Sol.get_model solver in
    begin
      (* Thresholds records how much of each 
       * variable is 'free'. *)
      let pred_map = build_pred_map solver obj in
      let obj_lb, thresholds = init_thresholds solver obj in
      (* match solve_core' print_nogood solver pred_map thresholds (k + obj_lb) with 
      | Some m' -> Opt m'
      | None -> Sat m
      *)
      (*
      match solve_core_strat print_model print_nogood solver obj_var m pred_map thresholds (next_coeff thresholds max_int) (k + obj_lb) with
      | Some m' -> Opt m'
      | None -> Sat m
      *)
      (*
      let obj_val = Sol.int_value m obj_var in
      let _ = Sol.post_atom solver (Sol.ivar_lt obj_var obj_val) in
      *)
      solve_core_strat print_model print_nogood print_penalty solver obj_var m pred_map thresholds (next_coeff thresholds max_int) [] (k + obj_lb) !Opts.limits
    end
  | Sol.UNSAT -> Unsat
  | Sol.UNKNOWN -> Unknown
   *)

let print_stats fmt stats obj_val =
  match !Opts.print_stats with
  | Opts.Suppress -> ()
  | Opts.Compact ->  
    begin
      Format.fprintf fmt "%d,%d,%d,%d,%d,%.02f@."
        (match obj_val with
          | Some k -> k
          | None -> 0)
        stats.Sol.solutions
        stats.Sol.restarts
        stats.Sol.conflicts
        stats.Sol.num_learnts
        stats.Sol.time
    end
  | Opts.Verbose ->
    begin
      let _ = match obj_val with
      | Some k -> Format.fprintf fmt "objective %d@." k
      | None -> ()
      in
      Format.fprintf fmt "%d solutions, %d conflicts, %d restarts@." stats.Sol.solutions stats.Sol.conflicts stats.Sol.restarts ;
      Format.fprintf fmt "%.02f seconds.@." stats.Sol.time ;
      Format.fprintf fmt "%d learnts, average size %f@."
        stats.Sol.num_learnts
        ((float_of_int stats.Sol.num_learnt_lits) /. (float_of_int stats.Sol.num_learnts))
    end

let get_options () =
  let defaults = Sol.default_options () in
  let rlimit = !Opts.restart_limit in
  { defaults with
    Sol.one_watch = !Opts.one_watch ;
    Sol.global_diff = !Opts.global_diff ;
    Sol.restart_limit =
      match rlimit with
      | Some r -> r
      | None -> defaults.Sol.restart_limit
  }
  
let set_polarity solver env pol_info =
  Array.iteri (fun i ctx ->
    match ctx with
    | { Pol.pos = false ; Pol.neg = true } ->
      Sol.set_bool_polarity solver env.bvars.(i) false
    | { Pol.pos = true ; Pol.neg = false } ->
      Sol.set_bool_polarity solver env.bvars.(i) true
    | _ -> ()
  ) pol_info.Pol.bvars ;
  Array.iteri (fun i ctx -> 
    match ctx with
    | { Pol.pos = false ; Pol.neg = true } ->
      Sol.set_int_polarity env.ivars.(i) false
    | { Pol.pos = true ; Pol.neg = false } ->
      Sol.set_int_polarity env.ivars.(i) true
    | _ -> ()
  ) pol_info.Pol.ivars

let get_core_limits limits =
  match !Opts.core_ratio with
  | None -> limits
  | Some core_frac ->
    let tmax = if limits.Sol.max_time > 0.0 then core_frac *. limits.Sol.max_time else 0.0 in
    let cmax = if limits.Sol.max_conflicts > 0 then int_of_float (core_frac *. (float_of_int limits.Sol.max_conflicts)) else 0 in
    { Sol.max_time = tmax ; Sol.max_conflicts = cmax }

let rebuild_objective solver thresholds lb ub =
  let ts = ref [] in
  H.iter (fun x st ->
    let sx = Sol.slice_rezero (Sol.slice_of_intvar x) st.lb in
    if st.residual <> st.coeff then
      (* Need to split into the first bit, and the rest. *)
      let s1 = Sol.slice_upto sx 1 in
      let sR = Sol.slice_rezero sx 1 in
      ts := (st.residual, s1) :: (st.coeff, sR) :: !ts 
    else
     ts := (st.coeff, sx) :: !ts) thresholds ;
  let rev_obj = Sol.new_intvar solver lb ub in
  let t_obj = (-1, Sol.slice_of_intvar rev_obj) in
  let _ = Builtins.slice_linear_le solver At.at_True (Array.of_list (t_obj :: !ts)) (- lb) in
  rev_obj
    
let minimize_uc print_model print_nogood get_ivar_name print_penalty solver obj xs k : Solver.model option =
    let fmt = Format.std_formatter in
    (* Format.fprintf fmt "[ k = %d ]@." k ; *)
    let overall_limits = !Opts.limits in
    match Sol.solve solver (relative_limits solver overall_limits) with
    | Sol.SAT ->
      (* Found a first model. *)
      let m = Sol.get_model solver in
      begin
        let _ = print_model Format.std_formatter m in
        let core_limits = get_core_limits overall_limits in
        (* )
        let ts = Array.to_list xs in
        (* let core_limits = overall_limits in *)
        let pred_map = build_pred_map solver ts in
        let obj_lb, thresholds = init_thresholds solver ts in
        (* Run stratified core-driven optimization until we use up our budget *)
        match solve_core_strat print_model print_nogood solver obj m pred_map thresholds (next_coeff thresholds max_int) [] (k + obj_lb) core_limits with ( *)
        let core_result =
          match !Opts.core_type with
          | Opts.SliceCore ->
             let ts = Array.to_list xs in
             let pred_map = build_pred_map solver ts in
             let obj_lb, thresholds = init_thresholds solver ts in
             solve_core_strat print_model print_nogood print_penalty solver obj m pred_map thresholds (next_coeff thresholds max_int) [] (k + obj_lb) core_limits
          | Opts.IntCore ->
            let core_config = {
            IntCore.print_model = print_model fmt ;
            IntCore.print_nogood = print_nogood fmt ;
            IntCore.ivar_name = get_ivar_name ;
            IntCore.limits = core_limits
            } in
            let core_state = IntCore.init_state obj xs k m in
            IntCore.solve core_config solver core_state
        in
        match core_result with
        (* *)
        | Sat (model, lb, thresholds) ->
          (* If we haven't proven optimality yet, reformulate the objective, and switch
           * to conventional branch-and-bound. *)
          (* Some model *)
          (* *)
          let ub = (Sol.int_value model obj) - 1 in
          let _ = Sol.retract_all solver in
          let revised_obj = rebuild_objective solver thresholds lb ub in
          (* let _ = Format.fprintf Format.err_formatter "%% Switching: [%d, %d|%d]@." lb ub (eval_obj model (revised_obj, Some (xs, k))) in *)
          begin
            let o = revised_obj in
            let _ = B.int_le solver At.at_True obj o 0 in
            (* let o = obj in *)
            match solve_minimize overall_limits print_model print_nogood solver (o, Some (xs, k)) [] with
            | None -> Some model
            | Some m ->
              (* let _ = Format.fprintf Format.err_formatter "%% {{%d | %d}} [%d]" (eval_obj m (revised_obj, Some (xs, k))) (Sol.int_value m obj) k in *)
              Some m
          end
          (* *)
        | Opt m ->
          (* Core-driven optimisation proved optimality. *)
          Format.fprintf fmt "==========@." ;
          Some m
        | _ -> failwith "Internal error: got Unsat or Unknown, even though we already have a model."
      end
    | Sol.UNSAT -> 
        Format.fprintf fmt "=====UNSATISFIABLE=====@." ;
        None
    | Sol.UNKNOWN -> None


let minimize_transpose print_model print_nogood solver obj xs k =
  (* FIXME *)
  Array.iter (fun (c, x) -> assert (c = 1)) xs ;
  let vs = Array.map snd xs in
  let lb = Array.fold_left (fun l x -> min l (Sol.ivar_lb x)) max_int vs in
  let ub = Array.fold_left (fun u x -> max u (Sol.ivar_ub x)) min_int vs in
  (* Build the penalty terms. *)
  let ps = Array.init (ub - lb) (fun i ->
    let k = lb + i + 1 in
    let p = Sol.new_intvar solver 0 (Array.length vs) in
    (* Relate penalty to core *)
    (* Now update thresholds *)
    let atoms = Array.map (fun v -> Sol.ivar_ge v k) vs in    
    let _ = post_bool_sum_geq solver p atoms (0) in
    p) in
  let obj_transpose = Sol.new_intvar solver (Sol.ivar_lb obj) (Sol.ivar_ub obj) in
  let ts = Array.map (fun x -> 1, x) ps in
  let _ = B.linear_le solver At.at_True (Array.append [|-1, obj_transpose|] ts) (- lb * (Array.length xs)) in
  solve_minimize !Opts.limits  print_model print_nogood solver (obj_transpose, None) []

let minimize_linear print_model print_nogood get_ivar_name print_penalty solver obj ts k =
  if !Opts.core_opt then
    (* Solve using unsat cores. *)
    let xs = Array.map (fun (c, x) ->
      if c > 0 then
        c, x
      else
        -c, Sol.intvar_neg x) ts in
    minimize_uc print_model print_nogood get_ivar_name print_penalty solver obj xs k
  else
    solve_minimize !Opts.limits print_model print_nogood solver (obj, None) []
    (*
    let xs = Array.map (fun (c, x) ->
      if c > 0 then
        c, x
      else
        -c, Sol.intvar_neg x) ts in
    minimize_transpose print_model print_nogood solver obj xs k *)

let collect_linterms defs env obj =
  let k = ref 0 in
  let ts = H.create 17 in
  (* Collect the set of terms. *)
  let rec aux coeff obj =
    match defs.(obj) with
    | Simp.Iv_const c -> k := !k + coeff * c
    | Simp.Iv_eq x -> aux coeff x
    | Simp.Iv_opp x -> aux (-coeff) x
    | Simp.Iv_lin (ts, c) ->
      begin
        k := !k + coeff * c ;
        Array.iter (fun (c, x) -> aux (c * coeff) x) ts
      end
    | _ ->
      begin
        let x = env.ivars.(obj) in
        try
          let cx = H.find ts x in
          H.replace ts x (cx + coeff)
        with Not_found -> H.add ts x coeff 
      end
  in
  aux 1 obj ; 
  (* Now produce an array *) 
  let ts_list = Hashtbl.fold (fun x c ts -> (c, x) :: ts) ts [] in
  Array.of_list ts_list, !k

(* Follow the objective chain definition, to set variable polarities. *)
let set_obj_polarity solver idefs bdefs env sign v =
  let seeni = H.create 17 in
  let seenb = H.create 17 in
  let rec auxi sign v =  
    try H.find seeni v
    with Not_found ->
      H.add seeni v () ;
      Sol.set_int_polarity env.ivars.(v) sign ;
      match idefs.(v) with
     (* Aliasing *)
     | Simp.Iv_eq v' -> auxi sign v'
     | Simp.Iv_opp v' -> auxi (not sign) v'
     (* Arithmetic functions *)
     | Simp.Iv_lin (ts, _) ->
      Array.iter (fun (c, x) -> if c > 0 then auxi sign x else auxi (not sign) x) ts
     | Simp.Iv_max xs -> Array.iter (auxi sign) xs
     | Simp.Iv_min xs -> Array.iter (auxi sign) xs
     | Simp.Iv_b2i b -> auxb sign b
     | _ -> ()
   and auxb sign b =
    try H.find seenb b
    with Not_found ->
      H.add seenb b () ;
      Sol.set_bool_polarity solver env.bvars.(b) sign ;
      match bdefs.(v) with
      | Simp.Bv_eq b' -> auxb sign b'
      | Simp.Bv_neg b' -> auxb (not sign) b'
      | Simp.At (x, Simp.Ile, _) -> auxi (not sign) x
      | Simp.At (x, Simp.Igt, _) -> auxi sign x
      | Simp.Bv_or bs -> Array.iter (auxb sign) bs
      | Simp.Bv_and bs -> Array.iter (auxb sign) bs
      | _ -> ()
  in auxi sign v
    
let main () =
  (* Parse the command-line arguments *)
  Arg.parse
    Opts.speclist
      (begin fun infile -> Opts.infile := Some infile end)
      "fzn_geas <options> <inputfile>"
  ;
  Half_reify.initialize () ;
  Registry.initialize () ;
  (* Parse the program *)
  let input = match !Opts.infile with
      | None -> stdin
      | Some file -> open_in file
  in
  let lexer = P.lexer input in
  let orig_problem = P.read_problem lexer in
  (* let pol_ctxs = Polarity.polarity orig_problem in *)
  let opts = get_options () in
  let solver = Sol.new_solver opts in
  try
    let s_problem = Simplify.simplify orig_problem in
    let ctxs = Polarity.polarity s_problem in
    (* Construct the problem *)
    (*
    let problem =
      if !Opts.half_reify then
        Half_reify.half_reify ~ctxs:pol_ctxs problem 
      else problem in
    *)
    let (idefs, bdefs, problem) = s_problem in
    (* Simp.log_reprs idefs bdefs ; *)
    (* let env = build_problem solver problem ctxs idefs bdefs in *)
    let env = Build.build_problem solver s_problem ctxs in
    (* Perform polarity analysis, to set branching *)
    let _ = if !Opts.pol then
      set_polarity solver env ctxs in
    let assumps =
      match get_ann_assumps problem env (snd problem.Pr.objective) with
      | None -> [ At.neg At.at_True ]
      | Some atoms -> atoms
    in
    build_branching problem env solver (snd problem.Pr.objective) ;
    (*
    let problem_HR =
      if !Opts.noop then
        problem
      else
        Half_reify.half_reify problem in
     *)
    let print_model =
      (fun fmt model ->
        if not !Opts.quiet then
          begin
            print_solution fmt problem env model ;
            Format.fprintf fmt "----------@."
          end) in
    let print_nogood = print_nogood problem env in
    let get_ivar_name = ivar_name problem env in
    let pp_atom = print_atom problem env in
    let print_penalty =
      if !Opts.verbosity > 2 then
        (fun fmt x core ->
          Format.fprintf fmt "%% VAR: %s = " (get_ivar_name x) ; 
          Util.print_array (fun fmt (c, at) ->
            Format.fprintf fmt "%d " c ;
            pp_atom fmt at) ~pre:"" ~post:"@." ~sep:" + " fmt core)
      else
        (fun fmt x core -> ())
    in
    let obj_val = ref None in
    begin
    match fst problem.Pr.objective with
    | Pr.Satisfy ->
       if !Opts.max_solutions = 1 then
          solve_satisfy print_model print_nogood solver assumps
       else
         let block = block_solution problem env in
         solve_findall print_model print_nogood block solver assumps
    | Pr.Minimize obj ->
        let r : Sol.model option = match idefs.(obj) with
          | Simp.Iv_lin _ ->
            let xs, k = collect_linterms idefs env obj in
            (* let xs = Array.map (fun (c, x) -> c, env.ivars.(x)) ts in *)
            minimize_linear print_model print_nogood get_ivar_name print_penalty solver env.ivars.(obj) xs k
          | _ ->
            solve_minimize !Opts.limits print_model print_nogood solver (env.ivars.(obj), None) []
        in
      begin
      match r with
      | Some m -> obj_val := Some (Sol.int_value m env.ivars.(obj))
      | None -> ()
      end
    | Pr.Maximize obj ->
        set_obj_polarity solver idefs bdefs env true obj ;
        let r = match idefs.(obj) with
          | Simp.Iv_lin _ ->
            (* let xs = Array.map (fun (c, x) -> -c, env.ivars.(x)) ts in *)
            let xs, k = collect_linterms idefs env obj in
            minimize_linear print_model print_nogood get_ivar_name print_penalty solver (Sol.intvar_neg env.ivars.(obj))
              (Array.map (fun (c, x) -> (-c, x)) xs) (-k)
          | _ ->
            solve_minimize !Opts.limits print_model print_nogood solver ((Sol.intvar_neg env.ivars.(obj)), None) []
        in
        begin
        match r with
        | Some m -> obj_val := Some (Sol.int_value m env.ivars.(obj))
        | None -> ()
        end
    end ;
    (* let fmt = Format.std_formatter in *)
    let fmt = Format.err_formatter in
    print_stats fmt (Sol.get_statistics solver) !obj_val
  with Pr.Root_failure ->
    let fmt = Format.err_formatter in
    Format.fprintf fmt "%%%% Model inconsistency detected.@." ;
    Format.fprintf fmt "=====UNSATISFIABLE=====@." ;
    print_stats fmt (Sol.get_statistics solver) None

let _ = main ()
