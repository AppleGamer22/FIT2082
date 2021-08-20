(** Replace full- with half-reification where possible *)
module Dy = DynArray
module H = Hashtbl

module U = Util
module HS = Util.HashSet

module Pr = Problem
module Pol = Polarity

let ctx_none = { Pol.pos = false ; Pol.neg = false }
let ctx_pos = { Pol.pos = true ; Pol.neg = false }
let ctx_neg = { Pol.pos = false ; Pol.neg = true }
let ctx_mixed = { Pol.pos = true; Pol.neg = true }

let get_ctx ctxs = function
  | Pr.Blit true -> ctx_pos
  | Pr.Blit false -> ctx_neg
  | Pr.Bvar b -> ctxs.Pol.bvars.(b)
  | Pr.Ilit _ -> ctx_mixed
  | Pr.Ivar v -> ctxs.Pol.ivars.(v)
  | _ -> failwith "Attempted to get context of non-Boolean"

let get_array expr = Pr.get_array (fun x -> x) expr

(* Assumption: all reified constraints give their definition last *)
let handlers = H.create 13

let default_handler ctxs id args ann = [((id, args), ann)]

let transform_constraint ctxs rs ((id, args), ann) =
  let handler =
    try H.find handlers id
    with Not_found -> default_handler in
  List.append (handler ctxs id args ann) rs

let half_reify ?ctxs:opt_ctxs s_model =
  let (idefs, bdefs, model) = s_model in
  (* Identify variables of interest *)
  let ctxs =
    match opt_ctxs with
    | None -> Polarity.polarity s_model
    | Some ctxs -> ctxs in
  begin
    if !Opts.verbosity > 0 then
      begin
        Util.print_array ~pre:"ivars: [|@[" ~post:"|]@]@."
          (fun fmt x -> Format.pp_print_string fmt (Polarity.ctx_string x))
          Format.err_formatter ctxs.Polarity.ivars ;
        Util.print_array ~pre:"bvars: [|@[" ~post:"|]@]@."
          (fun fmt x -> Format.pp_print_string fmt (Polarity.ctx_string x))
          Format.err_formatter ctxs.Polarity.bvars
      end
  end ;
  (* Annotate Boolean 'reification' vars. *)
  let bv_sz = Dy.length model.Pr.bvals in
  for ii = 0 to bv_sz-1 do
    if ctxs.Polarity.bvars.(ii) <> ctx_mixed then
      let id, anns = Dy.get model.Pr.bvals ii in
      Dy.set model.Pr.bvals ii (id, Pr.Ann_id "reif_var" :: anns)
  done ;
  let repl_constraints = Dy.fold_left (transform_constraint ctxs) [] model.Pr.constraints
        |> List.rev |> Dy.of_list in
  let model =
  { Pr.symbols = H.copy model.Pr.symbols ;
    Pr.ivals = Dy.copy model.Pr.ivals ;
    Pr.bvals = Dy.copy model.Pr.bvals ;
    Pr.constraints = repl_constraints ;
    Pr.objective = model.Pr.objective } in
  (idefs, bdefs, model)

let rewrite_and ctxs id args ann =
  let rvar = U.array_last args in
  match get_ctx ctxs rvar with
   (* Unconstrained. Ignore. *)
  | { Pol.pos = false; Pol.neg = false} -> []
  (* Positive only; half-reify *)
  | { Pol.pos = true; Pol.neg = false } ->
      [("bool_clause", [| Pr.Arr [|args.(0)|]; Pr.Arr [|rvar|]|]), ann ;
       ("bool_clause", [| Pr.Arr [|args.(1)|]; Pr.Arr [|rvar|]|]), ann]
  (* Negative only; ideally, should rewrite *)
  | { Pol.pos = false; Pol.neg = true } ->
      [("bool_clause", [| Pr.Arr [|rvar|] ; Pr.Arr [|args.(0) ; args.(1)|]|]), ann]
  | { Pol.pos = true ; Pol.neg = true } -> [((id, args), ann)]

let rewrite_array_and ctxs id args ann =
  let rvar = U.array_last args in
  match get_ctx ctxs rvar with
  | { Pol.pos = false ; Pol.neg = false } -> []
  | { Pol.pos = true ; Pol.neg = false } ->
      List.map
        (fun x -> ("bool_clause", [|Pr.Arr [|x|] ; Pr.Arr [|rvar|]|]), ann)
        (Array.to_list (get_array args.(0)))
  | { Pol.pos = false ; Pol.neg = true } ->
      [("bool_clause", [| Pr.Arr [|rvar|] ; args.(0) |]), ann]
  | { Pol.pos = true ; Pol.neg = true } -> [(id, args), ann]

let rewrite_array_or ctxs id args ann =
  let rvar = U.array_last args in
  match get_ctx ctxs rvar with
  | { Pol.pos = false ; Pol.neg = false } -> []
  | { Pol.pos = true ; Pol.neg = false } ->
      [("bool_clause", [| args.(0) ; Pr.Arr [|rvar|] |]), ann]
  | { Pol.pos = false ; Pol.neg = true } ->
      List.map
        (fun x -> ("bool_clause", [| Pr.Arr [|rvar|] ; Pr.Arr [|x|] |]), ann)
        (Array.to_list (get_array args.(0))) 
  | { Pol.pos = true ; Pol.neg = true } -> [(id, args), ann]

let rewrite_or ctxs id args ann =
  let rvar = U.array_last args in
   (* Unconstrained. Ignore. *)
  match get_ctx ctxs rvar with
  | { Pol.pos = false; Pol.neg = false} -> []
  (* Positive only *)
  | { Pol.pos = true; Pol.neg = false } ->
      [("bool_clause", [| Pr.Arr [|args.(0); args.(1)|]; Pr.Arr [|rvar|]|]), ann]
  (* Negative only *)
  | { Pol.pos = false; Pol.neg = true } ->
      [("bool_clause", [| Pr.Arr [|rvar|] ; Pr.Arr [|args.(0)|]|]), ann;
       ("bool_clause", [| Pr.Arr [|rvar|] ; Pr.Arr [|args.(1)|]|]), ann]
  | { Pol.pos = true ; Pol.neg = true } -> [((id, args), ann)]

let specialized_handlers =
  [ "bool_and", rewrite_and ;
    "bool_or", rewrite_or ;
    "array_bool_or", rewrite_array_or ;
    "array_bool_and", rewrite_array_and ]

let ($$) = Array.append

let rewrite_lin_le_pos _ args ann = [("int_lin_le_HR", args $$ [|Pr.Blit true|]), ann]
let rewrite_lin_le_neg _ args ann =
  let cs = Array.map (fun k -> Pr.Ilit (-k)) (Pr.get_array Pr.get_int args.(0)) in
  let k = Pr.Ilit (-1 - (Pr.get_int args.(2))) in
  [("int_lin_le_HR", [| Pr.Arr cs ; args.(1) ; k ; args.(3) ; Pr.Blit false |]), ann]
  
let rewrite_lin_eq_pos _ args ann = [("int_lin_eq_HR", args $$ [|Pr.Blit true|]), ann]
let rewrite_lin_eq_neg _ args ann = [("int_lin_ne_HR", args $$ [|Pr.Blit false|]), ann]

let rewrite_lin_ne_pos _ args ann = [("int_lin_ne_HR", args $$ [|Pr.Blit true|]), ann]
let rewrite_lin_ne_neg _ args ann = [("int_lin_eq_HR", args $$ [|Pr.Blit false|]), ann]

let rewrite_le_pos _ args ann = [("int_le_HR", args $$ [|Pr.Blit true|]), ann]
let rewrite_le_neg _ args ann = [("int_lt_HR", [|args.(1); args.(0); args.(2); Pr.Blit false|]), ann]

let rewrite_lt_pos _ args ann = [("int_lt_HR", args $$ [|Pr.Blit true|]), ann]
let rewrite_lt_neg _ args ann = [("int_le_HR", [|args.(1); args.(0); args.(2); Pr.Blit false|]), ann]

let rewrite_int_eq_pos _ args ann = [("int_eq_HR", args $$ [|Pr.Blit true|]), ann]
let rewrite_int_eq_neg _ args ann = [("int_ne_HR", args $$ [|Pr.Blit false|]), ann]

let rewrite_int_ne_pos _ args ann = [("int_ne_HR", args $$ [|Pr.Blit true|]), ann]
let rewrite_int_ne_neg _ args ann = [("int_eq_HR", args $$ [|Pr.Blit false|]), ann]

let rewrite_element_neg id args ann = [(id ^ "_LE", args), ann]
let rewrite_element_pos id args ann = [(id ^ "_GE", args), ann]

let rewrite_bool_le_pos _ args ann =
  [("bool_clause", [|Pr.Arr [|args.(1)|] ; Pr.Arr [|args.(0) ; args.(3)|]|]), ann]
let rewrite_bool_le_neg _ args ann =
  [("bool_clause", [|Pr.Arr [|args.(0); args.(3)|]; Pr.Arr [| |]|]), ann ;
   ("bool_clause", [|Pr.Arr [|args.(3)|] ; Pr.Arr [|args.(1)|]|]), ann]

let rewrite_bool_lt_pos _ args ann =
  [("bool_clause", [|Pr.Arr [|args.(1)|] ; Pr.Arr [|args.(3)|]|]), ann ;
   ("bool_clause", [|Pr.Arr [| |] ; Pr.Arr [|args.(0) ; args.(3)|]|]), ann]
let rewrite_bool_lt_neg _ args ann =
  [("bool_clause", [|Pr.Arr [|args.(1); args.(3)|] ; Pr.Arr [|args.(0)|]|]), ann]

let rewrite_bool_eqr_pos _ args ann =
  [("bool_clause", [|Pr.Arr [|args.(0)|]; Pr.Arr [|args.(1); args.(2)|]|]), ann ;
   ("bool_clause", [|Pr.Arr [|args.(1)|]; Pr.Arr [|args.(0); args.(2)|]|]), ann]
let rewrite_bool_eqr_neg _ args ann =
  [("bool_clause", [|Pr.Arr [|args.(0);args.(1);args.(2)|]; Pr.Arr [| |]|]), ann ;
   ("bool_clause", [|Pr.Arr [|args.(2)|]; Pr.Arr [|args.(0); args.(1)|]|]), ann]

let rewrite_setin_pos _ args ann = [("set_in_HR", args $$ [|Pr.Blit true|]), ann]
let rewrite_setin_neg _ args ann = [("set_notin_HR", args $$ [|Pr.Blit false|]), ann]

let reif_rewrites =
  [ (* Reified int relations *)
    "int_lin_le_reif", rewrite_lin_le_pos, rewrite_lin_le_neg ;
    "int_lin_eq_reif", rewrite_lin_eq_pos, rewrite_lin_eq_neg ;
    "int_lin_ne_reif", rewrite_lin_ne_pos, rewrite_lin_ne_neg ;
    "int_eq_reif", rewrite_int_eq_pos, rewrite_int_eq_neg ;
    "int_ne_reif", rewrite_int_ne_pos, rewrite_int_ne_neg ;
    "int_le_reif", rewrite_le_pos, rewrite_le_neg ;
    "int_lt_reif", rewrite_lt_pos, rewrite_lt_neg ;
    (* Reified bool relations *)
    "bool_eq_reif", rewrite_bool_eqr_pos, rewrite_bool_eqr_neg ;
    "bool_le_reif", rewrite_bool_le_pos, rewrite_bool_le_neg ;
    "bool_lt_reif", rewrite_bool_lt_pos, rewrite_bool_lt_neg ;
    (* Reified set relations *)
    (* "set_in_reif", rewrite_setin_pos, rewrite_setin_neg ; *)
    (* "array_int_element", rewrite_element_pos, rewrite_element_neg ; *) ]

let rewrite_reif f_pos f_neg ctxs id args ann =
  let rvar = U.array_last args in
  match get_ctx ctxs rvar with
  (* Unconstrained. Ignore. *)
  | { Pol.pos = false; Pol.neg = false} -> []
  (* Positive only; half-reify *)
  | { Pol.pos = true; Pol.neg = false } -> f_pos id args ann
  (* Negative only; ideally, should rewrite *)
  | { Pol.pos = false; Pol.neg = true } -> f_neg id args ann
  | { Pol.pos = true ; Pol.neg = true } -> [((id, args), ann)]

let register_handlers () =
  List.iter (fun (id, hnd) -> H.add handlers id hnd) specialized_handlers ;
  if not !Opts.native then
    List.iter (fun (id, f_pos, f_neg) -> H.add handlers id (rewrite_reif f_pos f_neg)) reif_rewrites

let initialize () =
  register_handlers ()
