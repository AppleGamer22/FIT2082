module S = Stream
module H = Hashtbl
module Dy = DynArray

module U = Util

module Pr = Problem
module Simp = Simplify
module Pol = Polarity

module Sol = Solver
module At = Atom

module B = Builtins

exception Unknown_constraint of string

let put = Format.fprintf


(* Process-independent atoms *)
type epred =
  | Ptrue
  | Pbool of int
  | Pge of int * int
  | Peq of int * int

type eatom =
  | Pos of epred
  | Neg of epred
 
(* type env = { ivars : Solver.intvar array ; bvars : Atom.atom array } *)
open Registry


let neg_eatom = function
  | Pos p -> Neg p
  | Neg p -> Pos p

let get_idom model x =
 let vinfo = Dy.get model.Pr.ivals x in
 vinfo.Pr.dom

let make_intvar solver dom =
  let lb, ub = Dom.bounds dom in
  (* Create the var *)
  let v = Sol.new_intvar solver lb ub in
  (* Punch any holes. post_clause should never fail here. *)
  let _ =
    match dom with
    | Dom.Set ks -> ignore (Sol.make_sparse v (Array.of_list ks))
    | _ -> () in
  (* Then return the constructed variable *)
  v

let prune_intvar s x dom =
  match dom with
  | Dom.Range (l, u) ->
    Sol.post_atom s (Sol.ivar_ge x l) && Sol.post_atom s (Sol.ivar_le x u)
  | Dom.Set ks -> Sol.make_sparse x (Array.of_list ks)

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
    with Not_found -> Format.fprintf fmt "??")

let print_nogood problem env =
  let pp_atom = print_atom problem env in
  (fun fmt nogood ->
    Util.print_array ~pre:"%% @[[" ~post:"]@]@." ~sep:",@ " pp_atom fmt nogood)

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
               
let post_constraint solver env ident exprs anns = 
  try
    (* let handler = H.find registry ident in *)
    let handler = Registry.lookup ident in
    (* let args = Array.map (resolve_expr env) exprs in 
    handler solver args anns *)
    handler solver env exprs anns
  with
  | Pr.Type_mismatch ->
    (Format.fprintf Format.err_formatter "Error: type mismatch in '%s'.@." ident ;
        false)
  | Not_found ->
     raise (Unknown_constraint ident)
       (*
    (Format.fprintf Format.err_formatter "Warning: Ignoring unknown constraint '%s'.@." ident ;
     Registry.register ident (fun _ _ _ -> true) ;
        true)
        *)

let rel_fun = function
  | Simp.Ile -> Sol.ivar_le
  | Simp.Ieq -> Sol.ivar_eq
  | Simp.Igt -> Sol.ivar_gt
  | Simp.Ine -> Sol.ivar_ne

type 'a val_inst =
  | Pending
  | Open
  | Closed of 'a

let linterm k x = (k, x)
let neg_coeff (k, x) = (-k, x)

let apply_lindef s ctx z ts k =
  let terms =
    Array.append
      [| linterm (-1) z |]
      (Array.map (fun (k, x) -> linterm k x) ts) in
  if (* ctx.Pol.neg *) true then
    ignore @@ B.linear_le s At.at_True terms (- k) ;
  if (* ctx.Pol.pos *) true then
    ignore @@ B.linear_le s At.at_True (Array.map neg_coeff terms) k
    (*
  ignore @@ B.linear_le s At.at_True (Array.map neg_coeff terms)
  *)


let apply_max s ctx z xs =
  match ctx with
  | { Pol.pos = true ; Pol.neg = _ } ->
    (* TODO: Add one-sided max propagator. *)
    ignore @@ B.int_max s At.at_True z xs
  | { Pol.pos = false ; Pol.neg = true } ->
    Array.iter (fun x -> ignore @@ B.int_le s At.at_True x z 0) xs
  | _ -> ()

let apply_min s ctx z xs =
  match ctx with
  | { Pol.pos = _; Pol.neg = true } ->
    failwith "TODO: Implement min propagator."
  | { Pol.pos = true; Pol.neg = false } ->
    Array.iter (fun x -> ignore @@ B.int_le s At.at_True z x 0) xs
  | _ -> ()

let build_idef s make_ivar make_bvar dom ctx def =
  let z =
    match def with
    | Simp.Iv_eq x -> make_ivar x
    | Simp.Iv_opp x -> Sol.intvar_neg (make_ivar x)
    | Simp.Iv_lin ([|1, x|], k) ->
      let x' = make_ivar x in
      (* Format.fprintf Format.err_formatter "[.] := [%d] + %d@." x k ; *)
      (* let _ = prune_intvar s x' (Dom.add dom (-k)) in *)
      Sol.intvar_plus x' k
    | Simp.Iv_lin ([|-1, x|], k) ->
      let x' = make_ivar x in
      (* Format.fprintf Format.err_formatter "[.] := -[%d] + %d@." x k ; *)
      let _ = prune_intvar s x' (Dom.neg (Dom.add dom (-k))) in
      Sol.intvar_plus (Sol.intvar_neg x') k
    | Simp.Iv_const k -> make_intvar s (Dom.range k k)
    | _ -> make_intvar s dom in
  let _ = match Simp.map_idef make_bvar make_ivar def with
    (* Should instead resolve const references *)
    | ( Simp.Iv_none
      | Simp.Iv_const _
      | Simp.Iv_eq _
      | Simp.Iv_lin ([|1, _|], _)
      | Simp.Iv_lin ([|-1, _|], _)
      ) -> ()
    | Simp.Iv_opp x -> ()
    (* Arithmetic functions *)
    | Simp.Iv_elem (ys, x) -> failwith "Implement"
    | Simp.Iv_lin (ts, k) -> apply_lindef s ctx z ts k
    | Simp.Iv_prod ys -> failwith "Implement"
    | Simp.Iv_b2i b -> 
      ignore @@ 
      (Sol.post_clause s [| Sol.ivar_ge z 1 ; At.neg b |] &&
       Sol.post_clause s [| Sol.ivar_le z 0 ; b |])
    | Simp.Iv_max xs -> apply_max s ctx z xs
    | Simp.Iv_min xs -> apply_min s ctx z xs
  in
  let _ = prune_intvar s z dom in
  z

let build_bdef s make_ivar make_bvar ctx def =
  match Simp.map_bdef make_bvar make_ivar def with
  | Simp.Bv_none -> Sol.new_boolvar s
  | Simp.Bv_const b -> if b then At.at_True else (At.neg At.at_True)
  | Simp.Bv_eq b -> b
  | Simp.Bv_neg b -> At.neg b
  | Simp.At (x, r, k) -> rel_fun r x k
  | Simp.Bv_or xs ->
    let z = Sol.new_boolvar s in
    begin
      if ctx.Pol.pos then
        ignore @@ Sol.post_clause s (Array.append [|At.neg z|] xs)
      else () ;
      if ctx.Pol.neg then
        Array.iter (fun x -> ignore @@ Sol.post_clause s [|z ; At.neg x|]) xs
      else () ;
      z
    end
  | Simp.Bv_and xs ->
    let z = Sol.new_boolvar s in
    begin
      if ctx.Pol.pos then
        Array.iter (fun x -> ignore @@ Sol.post_clause s [|At.neg z ; x|]) xs
      else () ;
      if ctx.Pol.neg then
        ignore @@ Sol.post_clause s (Array.append [|z|] (Array.map At.neg xs))
      else () ;
      z
    end

let make_vars s model ctxs idefs bdefs =
  let ivars = Array.make (Array.length idefs) Pending in
  let bvars = Array.make (Array.length bdefs) Pending in
  let rec make_ivar iv =
    match ivars.(iv) with
    | Closed v -> v
    | Open -> failwith "Error: cyclic definitions."
    | Pending ->
      begin
        ivars.(iv) <- Open ;
        let dom = get_idom model iv in
        let ctx = ctxs.Pol.ivars.(iv) in
        let def = idefs.(iv) in
        let v = build_idef s make_ivar make_bvar dom ctx def in
        ivars.(iv) <- Closed v ;
        v
      end
  and make_bvar bv =
    match bvars.(bv) with
    | Closed v -> v
    | Open -> failwith "Error: cyclic definitions." 
    | Pending ->
      begin
        (* Format.fprintf Format.err_formatter "b%d := %s@." bv (Simp.string_of_bdefn bdefs.(bv)) ; *)
        bvars.(bv) <- Open ;
        let ctx = ctxs.Pol.bvars.(bv) in
        let v = build_bdef s make_ivar make_bvar ctx bdefs.(bv) in
        bvars.(bv) <- Closed v ;
        v
      end
  in
  (Array.init (Array.length idefs) make_ivar,
   Array.init (Array.length bdefs) make_bvar)
(*
let make_atoms s ivars bdefs =
  let bvars = Array.make (Array.length bdefs) At.at_True in
  Array.iteri (fun i _ ->
    bvars.(i) <-
      match bdefs.(i) with
      | None -> Sol.new_boolvar s
      | Some (Simp.Bv_eq v) -> bvars.(v)
      | Some (Simp.Bv_neg v) -> At.neg bvars.(v)
      | Some (Simp.At (iv, rel, k)) ->
        rel_fun rel ivars.(iv) k) bvars ;
  bvars
  *)

(* let build_problem solver problem ctxs idefs bdefs = *)
let build_lookup ivars bvars : At.t -> eatom option =
  let imap = H.create 17 in
  let bmap = H.create 17 in 
  Array.iteri (fun i x -> H.add imap (Sol.ivar_pred x) (i, (Sol.ivar_ge x 0).At.value)) ivars ;
  Array.iteri (fun i at -> H.add bmap at i) bvars ;
  let ige_lookup at =
    let (x, v0) = H.find imap at.At.pid in
    Pos (Pge (x, Int64.to_int (Int64.sub at.At.value v0)))
  in
  let pos_lookup at =
    try ige_lookup at
    with Not_found ->
      Pos (Pbool (H.find bmap at))
  in
  (fun at ->
    try Some (pos_lookup at)
    with Not_found ->
      Some (neg_eatom (pos_lookup (At.neg at))))

let build_problem solver p ctxs =
  let (idefs, bdefs, problem) = p in
  (* Allocate variables *)
  let ivars, bvars = make_vars solver problem ctxs idefs bdefs in
  let env = { ivars = ivars; bvars = bvars } in
  (* Process constraints *)
  Dy.iteri (fun id ((ident, expr), anns) ->
           Sol.set_cons_id solver (id+1) ;
           if not (post_constraint solver env ident expr anns) then
             (* let _ = Format.fprintf Format.err_formatter
                       "%% Failure posting constraint %s/%d (%d)@:" ident (Array.length expr) (id+1) in *)
             raise Pr.Root_failure
           else
             ())
          problem.Pr.constraints ;
  (* Then, return the bindings *)
  env

let atom_lookup env = build_lookup env.ivars env.bvars

let atom_of_epred env p =
  match p with
  | Ptrue -> At.at_True
  | Pbool b -> env.bvars.(b)
  | Pge (x, k) -> Sol.ivar_ge env.ivars.(x) k
  | Peq (x, k) -> Sol.ivar_eq env.ivars.(x) k

let atom_of_eatom env at =
  match at with
  | Pos p -> atom_of_epred env p
  | Neg p -> At.neg (atom_of_epred env p)
