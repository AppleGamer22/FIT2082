(** Module for inferring polarity information *)
module U = Util
module H = Hashtbl
module HS = Util.HashSet
module Dy = DynArray
module Ar = Array
module Pr = Problem
module S = Simplify

let print_warning = Format.fprintf Format.err_formatter

type vref =
  | Int of Pr.ival_id
  | Bool of Pr.bval_id

type polarity =
  | Pos of vref
  | Neg of vref

type rule =
  | Define of vref
  | Fact of polarity
  | Rule of polarity * polarity


let get_brefs e = List.map (fun b -> Bool b) (Pr.expr_bvars e)
let get_irefs e = List.map (fun v -> Int v) (Pr.expr_ivars e)
let get_refs e = (get_brefs e) @ (get_irefs e)

type ctx = { pos : bool ; neg : bool }

type t = { ivars : ctx array ; bvars : ctx array }

type pol_state = {
  get_vidx : vref -> int ;
  defined : bool array ;
  pol : bool array ;
  rules : int list array ;
  rule_table : (int * int) HS.t
}

let get_idx state = function
  | Pos v -> 2 * (state.get_vidx v)
  | Neg v -> 2 * (state.get_vidx v) + 1

let empty_state model =
  let bool_sz = Dy.length model.Pr.bvals in
  let int_sz = Dy.length model.Pr.ivals in
  let sz0 = bool_sz + int_sz in
  let sz = 2 * sz0 in
  let vref_id = function
    | Bool bv -> bv
    | Int iv -> bool_sz + iv
  in
  let get_idx = function
    | Pos vr -> 2 * (vref_id vr)
    | Neg vr -> 2 * (vref_id vr) + 1
  in
  let state = 
    { get_vidx = vref_id ;
      defined = Array.make sz0 false ;
      pol = Array.make sz false ;
      rules = Array.make sz [] ;
      rule_table = HS.create 13 } in
  (* Make sure objective is taken into consideration *)
  begin
    match fst model.Pr.objective with
    | Pr.Satisfy -> ()
    | Pr.Maximize v -> state.pol.(get_idx (Pos (Int v))) <- true
    | Pr.Minimize v -> state.pol.(get_idx (Neg (Int v))) <- true
  end ;
  state

let rec propagate_pol state idx =
  if not state.pol.(idx) then
    begin
      state.pol.(idx) <- true ;
      List.iter (propagate_pol state) state.rules.(idx)
    end

let apply_polarity state pol = propagate_pol state (get_idx state pol)

let add_rule state = function
  | Define vref ->
    begin
      let idx = state.get_vidx vref in
      if not state.defined.(idx) then
        state.defined.(idx) <- true
      else
        (apply_polarity state (Pos vref) ; apply_polarity state (Neg vref))
    end
  | Fact pol -> apply_polarity state pol
  | Rule (pre, post) ->
      let pre_idx = get_idx state pre
      and post_idx = get_idx state post in
      if state.pol.(pre_idx) then
        propagate_pol state post_idx
      else
        if not (HS.elem state.rule_table (pre_idx, post_idx)) then
          begin
            state.rules.(pre_idx) <- post_idx :: state.rules.(pre_idx) ;
            HS.add state.rule_table (pre_idx, post_idx)
          end

(* Registry for rule generators *)
let handlers = H.create 13

(* Default: every variable occurring in the constraint
 * becomes mixed. *)
let default_handler model args ann =
  Array.fold_left
    (fun rs e ->
      List.fold_left (fun rs b -> Fact (Pos b) :: Fact (Neg b) :: rs) rs (get_refs e))
    [] args

let add_pos rs b = (Fact (Pos b) :: rs)
let add_neg rs b = (Fact (Neg b) :: rs)
let add_mixed rs b = (Fact (Pos b) :: Fact (Neg b) :: rs)

let boccurs_array f rs exprs = Array.fold_left (fun rs' e -> List.fold_left f rs' (get_brefs e)) rs exprs
let boccurs_list f rs exprs = List.fold_left (fun rs' e -> List.fold_left f rs' (get_brefs e)) rs exprs

let occurs_array f rs exprs = Array.fold_left (fun rs' e -> List.fold_left f rs' (get_refs e)) rs exprs
let occurs_list f rs exprs = List.fold_left (fun rs' e -> List.fold_left f rs' (get_refs e)) rs exprs

let handle_clause _ args _ =
  assert (Array.length args = 2) ;
  let pos = boccurs_list add_pos [] [args.(0)] in
  let all = boccurs_list add_neg pos [args.(1)] in
  all

let handle_reif_monotone _ args _ =
  match U.array_last args with
  | Pr.Blit true -> occurs_array add_pos [] (U.array_drop args)
  | Pr.Blit false -> occurs_array add_neg [] (U.array_drop args)
  | Pr.Bvar x ->
      let rx = Bool x in
      occurs_array
        (fun rs y -> Rule ((Pos rx), (Pos y)) :: Rule ((Neg rx), (Neg y)) :: rs)
        [Define rx] (U.array_drop args)
  | _ -> failwith "Error: expected Boolean in last position of reification."

let handle_reif_antitone _ args _ =
  match U.array_last args with
  | Pr.Blit true -> boccurs_array add_neg [] (U.array_drop args)
  | Pr.Blit false -> boccurs_array add_pos [] (U.array_drop args)
  | Pr.Bvar x ->
      let rx = Bool x in
      occurs_array
        (fun rs y -> Rule ((Pos rx), (Neg y)) :: Rule ((Neg rx), (Pos y)) :: rs)
        [Define rx] (U.array_drop args)
  | _ -> failwith "Error: expected Boolean in last position of reification."

let handle_reif_mixed _ args _ =
  match U.array_last args with
  | Pr.Blit true -> boccurs_array add_mixed [] (U.array_drop args)
  | Pr.Blit false -> boccurs_array add_mixed [] (U.array_drop args)
  | Pr.Bvar x ->
      let rx = Bool x in
      occurs_array
        (fun rs y -> Rule ((Pos rx), (Pos y)) :: Rule ((Neg rx), (Neg y))
                  :: Rule ((Pos rx), (Neg y)) :: Rule ((Neg rx), (Pos y)) :: rs)
        [Define rx] (U.array_drop args)
  | _ -> failwith "Error: expected Boolean in last position of reification."
   
let handle_noop _ args _ = []


let polarity_rules model ((id, args), ann) =
  try
    let handler = H.find handlers id in
    handler model args ann
  with Not_found ->
    ( (* print_warning "WARNING: Using default polarity handler for: %s@." id ; *)
     H.add handlers id default_handler ;
     default_handler model args ann )

let update_polarity model state cstr =
  List.iter (add_rule state) (polarity_rules model cstr)

let add_mono rs x y = Rule (Pos x, Pos y) :: Rule (Neg x, Neg y) :: rs
let add_anti rs x y = Rule (Pos x, Neg y) :: Rule (Neg x, Pos y) :: rs
let add_mix rs x y = add_mono (add_anti rs x y) x y

let handle_idef x def =
  let bx = Int x in
  match def with
  | S.Iv_none -> []
  | S.Iv_const _ -> []
  (* Aliasing *)
  | S.Iv_eq y -> add_mono [] bx (Int y)
  | S.Iv_opp y -> add_anti [] bx (Int y)
  (* Arithmetic functions *)
  | S.Iv_elem (ys, x) ->
    Ar.fold_left (fun rs y -> add_mono rs bx (Int y)) (add_mix [] bx (Int x)) ys
  | S.Iv_lin (ys, _) -> Ar.fold_left (fun rs (c, y) ->
      if c < 0 then
        add_anti rs bx (Int y)
      else
        add_mono rs bx (Int y)) [] ys
  | S.Iv_prod ys -> Ar.fold_left (fun rs y -> add_mix rs bx (Int y)) [] ys
  | S.Iv_max ys -> Ar.fold_left (fun rs y -> add_mono rs bx (Int y)) [] ys
  | S.Iv_min ys -> Ar.fold_left (fun rs y -> add_mono rs bx (Int y)) [] ys
  | S.Iv_b2i b -> add_mono [] bx (Bool b)

let handle_bdef x def =
  let bx = Bool x in
  match def with
  | S.Bv_none -> []
  | S.Bv_const _ -> []
  | S.Bv_eq y -> add_mono [] bx (Bool y)
  | S.Bv_neg y -> add_anti [] bx (Bool y)
  | S.At (y, r, k) ->
    begin
      match r with
      | S.Ile -> add_anti [] bx (Int y)
      | S.Ieq -> add_mix [] bx (Int y)
      | S.Igt -> add_mono [] bx (Int y)
      | S.Ine -> add_mix [] bx (Int y)
    end
  | S.Bv_or ys -> Ar.fold_left (fun rs y -> add_mono rs bx (Bool y)) [] ys
  | S.Bv_and ys -> Ar.fold_left (fun rs y -> add_mono rs bx (Bool y)) [] ys

let polarity (bdefs, idefs, model) =
  (* let pol = Array.init (Array.length vars) (fun _ -> { pos = true ; neg = true }) in *)
  (* pol[2i] = pos[i], pol[2i+1] = neg[i] *)
  let state = empty_state model in
  Dy.iter (update_polarity model state) model.Pr.constraints ;
  let bctx = Array.init (Dy.length model.Pr.bvals)
    (fun i -> { pos = state.pol.(get_idx state (Pos (Bool i))) ;
                neg = state.pol.(get_idx state (Neg (Bool i))) }) in
  let ictx = Array.init (Dy.length model.Pr.ivals)
    (fun i -> { pos = state.pol.(get_idx state (Pos (Int i))) ;
                neg = state.pol.(get_idx state (Neg (Int i))) }) in
  { ivars = ictx ; bvars = bctx }

let ctx_string ctx =
  match ctx.pos, ctx.neg with
  | true, true -> "*"
  | true, _ -> "+"
  | _, true -> "-"
  | _, _ -> "."

type variance =
  | Def
  | Mono
  | Anti
  | Bi
  | Cpos
  | Cneg
  | Cmix

let rules_eq a b = match a, b with
  | Pr.Bvar vx, Pr.Bvar vy ->
      let x, y = Bool vx, Bool vy in
      [ Rule (Pos x, Pos y); Rule (Pos y, Pos x);
        Rule (Neg x, Neg y); Rule (Neg y, Neg x) ]
  | (Pr.Blit true, Pr.Bvar v) | (Pr.Bvar v, Pr.Blit true) -> [ Fact (Pos (Bool v)) ]
  | (Pr.Blit false, Pr.Bvar v) | (Pr.Bvar v, Pr.Blit false) -> [ Fact (Neg (Bool v)) ]
  | _, _ -> []

let rules_ne a b = match a, b with
  | Pr.Bvar vx, Pr.Bvar vy ->
      let x, y = Bool vx, Bool vy in
      [ Rule (Pos x, Neg y); Rule (Pos y, Neg x);
        Rule (Neg x, Pos y); Rule (Neg y, Pos x) ]
  | (Pr.Blit true, Pr.Bvar v) | (Pr.Bvar v, Pr.Blit true) -> [ Fact (Neg (Bool v)) ]
  | (Pr.Blit false, Pr.Bvar v) | (Pr.Bvar v, Pr.Blit false) -> [ Fact (Pos (Bool v)) ]
  | _, _ -> []

let rules_bool2int b x = match b, x with
  | Pr.Bvar vx, Pr.Ivar vy ->
      let x, y = Bool vx, Int vy in
      [ Define x ;
        Rule (Pos x, Pos y); Rule (Pos y, Pos x);
        Rule (Neg x, Neg y); Rule (Neg y, Neg x) ]
  | Pr.Blit true, Pr.Ivar vx -> [ Fact (Pos (Int vx)) ]
  | Pr.Blit false, Pr.Ivar vx -> [ Fact (Neg (Int vx)) ]
  | Pr.Bvar vx, Pr.Ilit k ->
      if k > 0 then [ Fact (Pos (Bool vx)) ] else [ Fact (Neg (Bool vx)) ]
  | _, _ -> []


let collect_linear_rules r cs xs = 
  U.array_fold2 (fun rs a x ->
    match x with
    | Pr.Ilit k -> rs
    | Pr.Ivar v -> List.append (r a v) rs
    | _ -> failwith "Type mismatch in linear") [] cs xs

let rules_linear_le cs xs =
  collect_linear_rules
    (fun a x -> if a < 0 then [Fact (Pos (Int x))] else [Fact (Neg (Int x))]) cs xs


let rules_linear_le_reif cs xs r =
  match r with
    | Pr.Blit true ->
      collect_linear_rules
        (fun a x -> if a < 0 then [Fact (Pos (Int x))] else [Fact (Neg (Int x))]) cs xs
    | Pr.Blit false ->
      collect_linear_rules
        (fun a x -> if a > 0 then [Fact (Pos (Int x))] else [Fact (Neg (Int x))]) cs xs
    | Pr.Bvar b ->
      let rb = Bool b in
      collect_linear_rules
        (fun a x ->
          if a < 0 then
            [Rule (Pos rb, Pos (Int x)) ; Rule (Neg rb, Neg (Int x))]
          else
            [Rule (Pos rb, Neg (Int x)) ; Rule (Neg rb, Pos (Int x))]) cs xs
    | _ -> failwith "Type mismatch in lin_le_reif"

let coeff_of cs xs def =
  let sz = min (Array.length cs) (Array.length xs) in
  let rec aux k =
    if k < sz then
      match xs.(k) with
      | Pr.Ivar x when x = def -> Some cs.(k)
      | _ -> aux (k+1)
    else
      None
  in aux 0

let rec defined_var state = function
  | [] -> None
  | ann :: anns ->
    begin match ann with
    | Pr.Ann_call (c, args) when c = "defines_var" ->
      begin
        match Pr.resolve_ann state args.(0) with
        | Pr.Ivar v -> Some v
        | _ -> failwith "Annotation id resolves to non-ivar."
      end
    | _ -> defined_var state anns
    end
   
let rules_linear_def cs xs def =
  (*
  if !Opts.verbosity > 0 then
    Format.fprintf Format.err_formatter "rules_linear_def activated.@." ;
    *)
  match coeff_of cs xs def with
  | Some k when k < 0 ->
    (* Negative coeff of defined *)
    collect_linear_rules
      (fun a x ->
        if x = def then []
        else
          if a > 0 then
            [Rule (Pos (Int def), Pos (Int x)) ; Rule (Neg (Int def), Neg (Int x))]
          else
            [Rule (Neg (Int def), Pos (Int x)) ; Rule (Pos (Int def), Neg (Int x))]) cs xs
  | Some k ->
    (* Defined has positive coeff *)
    collect_linear_rules
      (fun a x ->
        if x = def then []
        else
          if a < 0 then
            [Rule (Pos (Int def), Pos (Int x)) ; Rule (Neg (Int def), Neg (Int x))]
          else
            [Rule (Neg (Int def), Pos (Int x)) ; Rule (Pos (Int def), Neg (Int x))]) cs xs
  | _ -> failwith "No occurrences of defined var"

let dispatch_arg (m, a, b, d, rs) tx v =
  match tx with
    | Mono -> (v :: m, a, b, d, rs)
    | Anti -> (m, v :: a, b, d, rs)
    | Bi -> (m, a, v :: b, d, rs)
    | Def -> (m, a, b, v :: d, (Define v) :: rs)
    | Cpos -> (m, a, b, d, Fact (Pos v) :: rs)
    | Cneg -> (m, a, b, d, Fact (Neg v) :: rs)
    | Cmix -> (m, a, b, d, Fact (Pos v) :: Fact (Neg v) :: rs)

let split_args kinds args =
  U.array_fold2 (fun ss tx arg ->
    List.fold_left (fun ss v -> dispatch_arg ss tx v) ss (get_refs arg)
    (*
    match x with
    | Pr.Ilit _ -> ss
    | Pr.Blit _ -> ss
    | Pr.Ivar x -> dispatch_arg ss tx (Int x)
    | Pr.Bvar b -> dispatch_arg ss tx (Bool b)
    | _ -> failwith "Type mismatch in split_args"
    *)
  ) ([], [], [], [], []) kinds args

let handle_fundef kinds _ args _ = 
  let mono, anti, bi, defs, rs0 = split_args kinds args in
  List.fold_left (fun rs d ->
    let mrules = List.fold_left (fun rs m ->
      Rule (Pos d, Pos m) :: Rule (Neg d, Neg m) :: rs) rs (mono @ bi) in
    let arules = List.fold_left (fun rs a ->
      Rule (Pos d, Neg a) :: Rule (Neg d, Pos a) :: rs) mrules (anti @ bi) in
    arules
  ) rs0 defs

let handle_rel kinds _ args _ = 
  let sz = Array.length kinds in
  let rec aux rs k =
    if k >= sz then
      rs
    else
      let app =
        match kinds.(k) with
        | Mono | Cpos -> (fun rs x -> Fact (Pos x) :: rs)
        | Anti | Cneg -> (fun rs x -> Fact (Neg x) :: rs)
        | Bi | Cmix -> (fun rs x -> Fact (Pos x) :: Fact (Neg x) :: rs)
        | Def -> failwith "Unexpected definition in relation." in
      let rs' = List.fold_left app rs (get_refs args.(k)) in
      aux rs' (k+1)
  in aux [] 0

(* Register handlers *)
let specific_handlers = 
  ["array_bool_or", handle_reif_monotone ;
   "array_bool_and", handle_reif_monotone ;
   (* "array_bool_xor", handle_reif_mixed ; *)
   "bool_clause", handle_clause ;
   "bool_and", handle_reif_monotone ;
   "bool_eq", (fun _ args _ -> rules_eq args.(0) args.(1)) ;
   "bool_not", (fun _ args _ -> rules_ne args.(0) args.(1)) ;
   "bool2int", (fun _ args _ -> rules_bool2int args.(0) args.(1)) ;
   "bool_or", handle_reif_monotone ;
   (* "bool_xor", default_handler ; *)
   "bool_eq_reif", handle_reif_mixed ;
   "bool_le_reif", handle_fundef [|Anti; Mono; Def|] ;
   "bool_lt_reif", handle_fundef [|Anti; Mono; Def|] ;
   "int_eq", (fun model args anns ->
      match defined_var model anns with
      | Some v -> rules_linear_def [|1; -1|] [|args.(0); args.(1)|] v
      | None -> default_handler model args anns) ;
   "int_abs", handle_fundef [|Bi; Def|] ;
   "int_eq_reif", handle_reif_mixed ;
   "int_le_reif", handle_fundef [|Anti; Mono; Def|]  ;
   "int_lin_le", (fun _ args _ -> 
     let cs = Pr.get_array Pr.get_int args.(0)
     and xs = Pr.get_array (fun x -> x) args.(1) in
     rules_linear_le cs xs) ;
   "int_lin_eq", (fun model args anns ->
      match defined_var model anns with
      | Some v ->
        let cs = Pr.get_array Pr.get_int args.(0)
        and xs = Pr.get_array (fun x -> x) args.(1) in
        rules_linear_def cs xs v
      | _ -> default_handler model args anns) ;
   "int_lin_eq_reif", handle_reif_mixed ;
   "int_lin_le_reif",
     (fun _ args _ ->
       let cs = Pr.get_array Pr.get_int args.(0)
       and xs = Pr.get_array (fun x -> x) args.(1) in
       rules_linear_le_reif cs xs args.(3)) ;
   "int_lin_ne_reif", handle_reif_mixed  ;
   "int_lt", handle_rel [|Anti; Mono|] ;
   "int_le", handle_rel [|Anti; Mono|] ;
   "int_lt_reif", handle_fundef [|Anti; Mono; Def|] ;
   "int_ne_reif", handle_reif_mixed ;
   (* Arithmetic operators *) 
   "int_plus", handle_fundef [|Mono; Mono; Def|] ;
   "int_negate", handle_fundef [|Anti; Def|] ;
   "int_minus", handle_fundef [|Mono; Anti; Def|] ;
   "int_times", handle_fundef [|Bi; Bi; Def|] ; (* FIXME - need to look at domain sign *)
   "int_div", handle_fundef [|Bi; Cmix; Def|] ;
   "int_max", handle_fundef [|Mono; Mono; Def|] ;
   "int_min", handle_fundef [|Mono; Mono; Def|] ;
   (* Element versions *)
   "array_bool_element", handle_fundef [|Cmix; Mono; Def |] ;
   "array_var_bool_element", handle_fundef [|Cmix; Mono; Def|] ;
   "array_int_element", handle_fundef [|Cmix; Mono; Def|] ;
   "array_var_int_element", handle_fundef [|Cmix; Mono; Def|] ;
   (* Set constraints *)
   (* "set_in_reif", handle_fundef [|Bi; Bi; Def|] ; *)
   (* Globals *) 
   (*
   "bool_sum_le", handle_rel [|Anti; Mono|] ;
   "bool_sum_ge", handle_rel [|Mono; Anti|] ;
   "bool_sum_eq", handle_fundef [|Mono; Def|] ;
   *)
   "array_int_maximum", handle_fundef [|Def; Mono|] ;
   "cumulatives", handle_rel [|Cmix; Cneg; Cneg; Cpos|] ;
   "chuffed_cumulative", handle_rel [|Cmix; Cneg; Cneg; Cpos|] ;
   "chuffed_cumulative_vars", handle_rel [|Cmix; Cneg; Cneg; Cpos|] ]


let register_handlers () =
  List.iter (fun (id, hnd) -> H.add handlers id hnd) specific_handlers
let _ = register_handlers ()
