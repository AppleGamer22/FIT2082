(** Problem simplification *)
(* Not doing full EUF-style congruence closure -- 
 * just simple aliasing.
 * TODO: Add structural hashing. *)
module H = Hashtbl
module Dy = DynArray

module Pr = Problem

type bval_id = int
type ival_id = int

type kind = 
  | Bool
  | Int of Dom.t
type irel = Ile | Ieq | Igt | Ine
let negate_rel = function
  | Ile -> Igt
  | Igt -> Ile
  | Ieq -> Ine
  | Ine -> Ieq

let eval_rel r a b =
  match r with
  | Ile -> a <= b
  | Igt -> a > b
  | Ieq -> a = b
  | Ine -> a <> b

type ('b, 'i) idef = 
  | Iv_none
  | Iv_const of int
  (* Aliasing *)
  | Iv_eq of 'i
  | Iv_opp of 'i
  (* Arithmetic functions *)
  (* Maybe make this linear, rather than sum. *)
  | Iv_elem of ('i array * 'i)
  | Iv_lin of (int * 'i) array * int
  | Iv_prod of 'i array
  | Iv_max of 'i array
  | Iv_min of 'i array
  | Iv_b2i of 'b

let eval_idef z def =
  match def with
  | Iv_none -> z
  | Iv_const k -> k
  | Iv_eq x -> x
  | Iv_opp x -> -x
  | Iv_elem (ys, x) -> ys.(x)
  | Iv_lin (ts, k) -> Array.fold_left (fun s (c, x) -> s + c*x) k ts
  | Iv_prod xs -> Array.fold_left ( * ) 1 xs
  | Iv_min xs -> Array.fold_left min max_int xs
  | Iv_max xs -> Array.fold_left max min_int xs
  | Iv_b2i b -> if b then 1 else 0

let negate_idef = function
  | Iv_const k -> Some (Iv_const (-k))
  | Iv_eq x -> Some (Iv_opp x)
  | Iv_opp x -> Some (Iv_eq x)
  | Iv_lin (ts, k) -> Some (Iv_lin (Array.map (fun (k, x) -> (-k, x)) ts, -k))
  | _ -> None

let negatable_idef = function
  | Iv_const _
    | Iv_eq _
    | Iv_opp _
    | Iv_lin _ -> true
  | _ -> false
       
type ('b, 'i) bdef =
  | Bv_none
  | Bv_const of bool
  | Bv_eq of 'b
  | Bv_neg of 'b
  | At of 'i * irel * int
  | Bv_or of 'b array
  | Bv_and of 'b array

let eval_bdef z def =
  match def with
  | Bv_none -> z
  | Bv_const b -> b
  | Bv_eq b -> b
  | Bv_neg b -> not b
  | At (x, r, k) -> eval_rel r x k
  | Bv_or xs -> Array.fold_left (||) false xs
  | Bv_and xs -> Array.fold_left (&&) true xs

type bdefn = (bval_id, ival_id) bdef
type idefn = (bval_id, ival_id) idef

let negate_bdef = function
  | Bv_const b -> Some (Bv_const (not b))
  | Bv_eq x -> Some (Bv_neg x)
  | Bv_neg x -> Some (Bv_eq x)
  | At (x, r, k) -> Some (At (x, negate_rel r, k))
  | _ -> None

let negatable_bdef = function
  | Bv_const _
    | Bv_eq _
    | Bv_neg _
    | At _ -> true
  | _ -> false

let force_option = function
  | Some x -> x
  | None -> failwith "Error: called force_option on None"
          
let apply_snd f (a, b) = (a, f b)

let map_idef fb fi def =
  match def with
  | Iv_none -> Iv_none
  | Iv_const k -> Iv_const k
  | Iv_eq x -> Iv_eq (fi x)
  | Iv_opp x -> Iv_opp (fi x)
  | Iv_elem (ys, x) -> Iv_elem (Array.map fi ys, fi x)
  | Iv_lin (ts, k) -> Iv_lin (Array.map (apply_snd fi) ts, k)
  | Iv_prod xs -> Iv_prod (Array.map fi xs)
  | Iv_max xs -> Iv_max (Array.map fi xs)
  | Iv_min xs -> Iv_min (Array.map fi xs)
  | Iv_b2i b -> Iv_b2i (fb b)

let map_bdef fb fi def =
  match def with
  | Bv_none -> Bv_none
  | Bv_const b -> Bv_const b
  | Bv_eq b -> Bv_eq (fb b)
  | Bv_neg b -> Bv_neg (fb b)
  | At (x, r, k) -> At (fi x, r, k)
  | Bv_or xs -> Bv_or (Array.map fb xs)
  | Bv_and xs -> Bv_and (Array.map fb xs)

type t = ((idefn array) * (bdefn array) * Problem.t)

let irel_neg = function
  | Ile -> Igt
  | Igt -> Ile
  | Ieq -> Ine
  | Ine -> Ieq

let rel_str = function
  | Ile -> "<="
  | Igt -> ">"
  | Ieq -> "="
  | Ine -> "!="

let string_of_bdefn b =
  match b with
  | Bv_none -> "none"
  | Bv_const b -> string_of_bool b
  | Bv_eq b -> Format.sprintf "[b%d]" b
  | Bv_neg b -> Format.sprintf "~[b%d]" b
  | At (x, r, k) -> Format.sprintf "[x%d %s %d]" x (rel_str r) k
  | Bv_or xs -> "[or ...]"
  | Bv_and xs -> "[and ...]"

let string_of_idefn d =
  match d with
  | Iv_none -> "nil"
  | Iv_const k -> "const"
  | Iv_eq x -> "alias"
  | Iv_opp x -> "neg"
  | Iv_elem (ys, x) -> "elem"
  | Iv_lin (ts, k) -> "lin"
  | Iv_prod xs -> "prod"
  | Iv_max xs -> "max"
  | Iv_min xs -> "min"
  | Iv_b2i b -> "b2i"

let fzn_irel rel x y =
  match rel with
  | Ile -> (("int_le", [|x; y|]), [])
  | Igt -> (("int_lt", [|y; x|]), [])
  | Ieq -> (("int_eq", [|x; y|]), [])
  | Ine -> (("int_ne", [|x; y|]), [])

let fzn_irel_reif rel r x y =
  match r with
  | Pr.Blit true -> fzn_irel rel x y
  | Pr.Blit false -> fzn_irel (irel_neg rel) x y
  | _ -> 
    match rel with
    | Ile -> (("int_le_reif", [|x; y; r|]), [])
    | Igt -> (("int_lt_reif", [|y; x; r|]), [])
    | Ieq -> (("int_eq_reif", [|x; y; r|]), [])
    | Ine -> (("int_ne_reif", [|x; y; r|]), [])
  
type state = {
  idefs : idefn array ;
  bdefs : bdefn array ;
  cons : (Pr.cstr * Pr.ann_expr list) Dy.t
}

let registry = H.create 17

let init_state pr =
  { idefs = Array.make (Dy.length pr.Pr.ivals) Iv_none ;
    bdefs = Array.make (Dy.length pr.Pr.bvals) Bv_none ;
    cons = Dy.create () }

(* Dealing with signed union-find stuff *)
(* Neg should only appear with Bool-kind values *)
type 'a rep =
  | Pos of 'a
  | Neg of 'a
let neg_rep = function
  | Pos v -> Neg v
  | Neg v -> Pos v

let bdef_of_rep = function
  | Pos v -> Bv_eq v
  | Neg v -> Bv_neg v

let idef_of_rep = function
  | Pos v -> Iv_eq v
  | Neg v -> Iv_opp v

let rec brepr st v =
  match st.bdefs.(v) with
  | Bv_eq p ->
    let d = brepr st p in
    (st.bdefs.(v) <- bdef_of_rep d ; d)
  | Bv_neg p ->
    let d = neg_rep (brepr st p) in
    (st.bdefs.(v) <- bdef_of_rep d ; d)
  | _ -> Pos v
and irepr st v =
  match st.idefs.(v) with
  | Iv_eq p ->
    let d = irepr st p in
    (st.idefs.(v) <- idef_of_rep d ; d)
  | Iv_opp p ->
    let d = neg_rep (irepr st p) in
    (st.idefs.(v) <- idef_of_rep d ; d)
  | _ -> Pos v

let irepr_eq st v =
  let rec aux v =
    match st.idefs.(v) with
    | Iv_eq p ->
      let u = aux p in
      (st.idefs.(v) <- Iv_eq u ; u)
    | _ -> v
  in aux v
let brepr_eq st v =
  let rec aux v =
    match st.bdefs.(v) with
    | Bv_eq p ->
      let u = aux p in
      (st.bdefs.(v) <- Bv_eq u ; u)
    | _ -> v
  in aux v
    
let to_bvars xs = Pr.Arr (Array.map (fun y -> Pr.Bvar y) xs)
let to_ivars xs = Pr.Arr (Array.map (fun y -> Pr.Ivar y) xs)

let fzn_assert_beq st x def =
  Dy.add st.cons
    begin match def with
      | Bv_none
      | Bv_const _
      | Bv_eq _ | Bv_neg _ -> failwith "fzn_assert_beq called on alias."
      | At (y, r, k) ->
        fzn_irel_reif r (Pr.Bvar x) (Pr.Ivar y) (Pr.Ilit k)
      | Bv_or ys -> (("array_bool_or", [| to_ivars ys ; Pr.Bvar x |]), [])
      | Bv_and ys -> (("array_bool_and", [| to_ivars ys ; Pr.Bvar x |]), [])
    end

let fzn_assert_ieq st x def =
  Dy.add st.cons
  begin match def with
  | Iv_none
  | Iv_const _ 
  | Iv_eq _
  | Iv_opp _ -> failwith "fzn_assert_ieq called on alias."
  (* Arithmetic functions *)
  | Iv_elem (ys, x) -> failwith "FIXME"
  | Iv_lin (ts, k) ->
    (("int_lin_eq",
      [| Pr.Arr (Array.append [|Pr.Ilit (-1)|] (Array.map (fun (c, _) -> Pr.Ilit c) ts)) ;
         Pr.Arr (Array.append [|Pr.Ivar x|] (Array.map (fun (_, y) -> Pr.Ivar y)  ts)) ;
          Pr.Ilit (-k) |]), [])
  | Iv_prod xs -> failwith "FIXME"
  | Iv_max xs -> (("array_int_maximum", [| Pr.Ivar x; to_ivars xs |]), [])
  | Iv_min xs -> (("array_int_minimum", [| Pr.Ivar x; to_ivars xs |]), [])
  | Iv_b2i b -> (("bool2int", [| Pr.Bvar b; Pr.Ivar x |]), [])
  end
 
(* Precondition - v and v' are class reprs. *)
let beq_def st invert x = if invert then Bv_neg x else Bv_eq x

let evict_bdef st invert x y =
  let ry = st.bdefs.(y) in 
  (st.bdefs.(y) <- beq_def st invert x ;
   fzn_assert_beq st y ry)
 
let rec apply_bdef st v0 d =
  let v = brepr_eq st v0 in
  let dv = st.bdefs.(v) in
  match dv, d with
  | Bv_none, Bv_eq u0 ->
     let u = brepr_eq st u0 in
     (if u <> v then st.bdefs.(v) <- Bv_eq u)
  | Bv_none, Bv_neg u0 ->
     let u = brepr_eq st u0 in
     (if u = v then
        raise Pr.Root_failure
      else st.bdefs.(v) <- Bv_neg u)
  | Bv_none, def | def, Bv_none ->
     st.bdefs.(v) <- def
  | Bv_neg v0', def' when negatable_bdef def' -> 
     let v' = brepr_eq st v0' in
     let n_def = negate_bdef def' |> force_option in
     apply_bdef st v' n_def
  | def, Bv_eq u0 ->
     (* Unifying. *)
     let u = brepr_eq st u0 in
     let du = st.bdefs.(u) in
     if u <> v then
       begin
         match du with
         | Bv_none -> st.bdefs.(u) <- Bv_eq v
         | def' -> (st.bdefs.(u) <- Bv_eq v ; fzn_assert_beq st v def')
       end
  | def, Bv_neg u0 when negatable_bdef def ->
     let u = brepr_eq st u0 in
     let n_def = negate_bdef def |> force_option in
     begin
     if u = v then
       raise Pr.Root_failure
     else
       st.bdefs.(v) <- Bv_neg u ; apply_bdef st u n_def
     end
  (* TODO: Other cases *)
  | Bv_const a, Bv_const b -> (if a <> b then raise Pr.Root_failure)
  | def, Bv_const b -> (st.bdefs.(v) <- Bv_const b ; fzn_assert_beq st v def)
  | _, def' -> fzn_assert_beq st v def'

and apply_idef st v0 d =
  let v = irepr_eq st v0 in
  let dv = st.idefs.(v) in
  match dv, d with
  | Iv_none, Iv_eq u0 ->
     let u = irepr_eq st u0 in
     (if u <> v then st.idefs.(v) <- Iv_eq u)
  | Iv_none, Iv_opp u0 ->
     let u = irepr_eq st u0 in
     (if u = v then
        st.idefs.(v) <- Iv_const 0
      else
        st.idefs.(v) <- Iv_opp u)
  | Iv_none, def | def, Iv_none ->
     st.idefs.(v) <- def
  | Iv_b2i v', Iv_b2i u' -> apply_bdef st v' (Bv_eq u')
  | Iv_opp v0', def' when negatable_idef def' -> 
     let v' = irepr_eq st v0' in
     let n_def = negate_idef def' |> force_option in
     apply_idef st v' n_def
  | def, Iv_eq u0 ->
     (* Unifying. *)
     let u = irepr_eq st u0 in
     let du = st.idefs.(u) in
     if u <> v then
       begin
         match du with
         | Iv_none -> st.idefs.(u) <- Iv_eq v
         | def' -> (st.idefs.(u) <- Iv_eq v ; fzn_assert_ieq st v def')
       end
  | def, Iv_opp u0 when negatable_idef def ->
     let u = irepr_eq st u0 in
     let n_def = negate_idef def |> force_option in
     begin
     if u = v then
       (st.idefs.(v) <- Iv_const 0 ; fzn_assert_ieq st v def)
     else
       (st.idefs.(v) <- Iv_opp u ; apply_idef st u n_def)
     end
  (* TODO: Other cases *)
  | Iv_const a, Iv_const b -> (if a <> b then raise Pr.Root_failure)
  | def, Iv_const k -> (st.idefs.(v) <- Iv_const k ; fzn_assert_ieq st v def)
  | _, def' -> fzn_assert_ieq st v def'

let set_bool st x b = apply_bdef st x (Bv_const b)
let set_int st x k = apply_idef st x (Iv_const k)

let simp_irel_reif rel pr st args anns =
  let r = Pr.get_bval args.(2) in
  match r with
  | Pr.Bv_bool true ->
    Dy.add st.cons (fzn_irel rel args.(0) args.(1))
  | Pr.Bv_bool false ->
    Dy.add st.cons (fzn_irel (irel_neg rel) args.(0) args.(1))
  | Pr.Bv_var b ->
    let x = Pr.get_ival args.(0) in
    let y = Pr.get_ival args.(1) in
    begin
      match x, y with
      | Pr.Iv_int u, Pr.Iv_int v ->
        let res = match rel with
          | Ile -> u <= v
          | Ieq -> u = v
          | Igt -> u > v
          | Ine -> u <> v in
        (* (Format.fprintf Format.err_formatter "%d,%d|%s@." u v (if res then "true" else "false") ;
        set_bool st b res) *)
        set_bool st b res
      | Pr.Iv_var x, Pr.Iv_int k ->
        apply_bdef st b (At (x, rel, k))
      | Pr.Iv_int k, Pr.Iv_var x ->
        let def = match rel with
          | Ile -> At (x, Igt, k-1)
          | Ieq -> At (x, Ieq, k)
          | Igt -> At (x, Ile, k-1)
          | Ine -> At (x, Ine, k)
        in
        apply_bdef st b def
      | Pr.Iv_var x, Pr.Iv_var y ->
        Dy.add st.cons (fzn_irel_reif rel (Pr.Bvar b) (Pr.Ivar x) (Pr.Ivar y))
      (* | _, _ -> Dy.add st.cons (fzn_irel_reif rel (Pr.Bvar b) args.(0) args.(1)) *)
    end

let simp_bool_eq pr st args anns =
  match Pr.get_bval args.(0), Pr.get_bval args.(1) with
  | Pr.Bv_bool x, Pr.Bv_bool y -> if x <> y then
  (* failwith "Found toplevel conflict in bool_eq" *)
     raise Pr.Root_failure
  | (Pr.Bv_bool b, Pr.Bv_var x
  |  Pr.Bv_var x, Pr.Bv_bool b) ->
    (* Dy.add st.cons (("bool_eq", [|Pr.Bvar x ; Pr.Blit b|]), anns) *)
    apply_bdef st x (Bv_const b)
  | Pr.Bv_var x, Pr.Bv_var y -> apply_bdef st x (Bv_eq y)
  (*
  | Pr.Bv_var x, Pr.Bv_var y -> 
    Dy.add st.cons (("bool_eq", [|Pr.Bvar x; Pr.Bvar y|]), anns)
    *)

 let simp_bool_ne pr st args anns =
  match Pr.get_bval args.(0), Pr.get_bval args.(1) with
  | Pr.Bv_bool x, Pr.Bv_bool y -> if x = y then
    (* failwith "Found toplevel conflict in bool_ne"  *)
    raise Pr.Root_failure
  | (Pr.Bv_bool b, Pr.Bv_var x
  |  Pr.Bv_var x, Pr.Bv_bool b) ->
    (* Dy.add st.cons (("bool_ne", [|Pr.Bvar x ; Pr.Blit (not b)|]), anns) *)
    apply_bdef st x (Bv_const (not b))
  | Pr.Bv_var x, Pr.Bv_var y -> apply_bdef st x (Bv_neg y)

let simp_bool_eq_reif pr st args anns =
  match Pr.get_bval args.(2), Pr.get_bval args.(0), Pr.get_bval args.(1) with
  | Pr.Bv_bool z, Pr.Bv_bool x, Pr.Bv_bool y ->
    if z <> (x = y) then
      (* failwith "Found toplevel conflict in bool_eq_reif." *)
      raise Pr.Root_failure
  | Pr.Bv_bool a, Pr.Bv_bool b, Pr.Bv_var x
  | Pr.Bv_bool a, Pr.Bv_var x, Pr.Bv_bool b
  | Pr.Bv_var x, Pr.Bv_bool a, Pr.Bv_bool b ->
    apply_bdef st x (Bv_const (a=b)) 
  | Pr.Bv_bool a, Pr.Bv_var x, Pr.Bv_var y
  | Pr.Bv_var x, Pr.Bv_bool a, Pr.Bv_var y
  | Pr.Bv_var x, Pr.Bv_var y, Pr.Bv_bool a ->
    apply_bdef st x (if a then (Bv_eq y) else (Bv_neg y))
  | Pr.Bv_var z, Pr.Bv_var x, Pr.Bv_var y ->
    Dy.add st.cons (("bool_eq_reif", [|Pr.Bvar x; Pr.Bvar y; Pr.Bvar z|]), anns)

let simp_int_eq pr st args anns =
  match Pr.get_ival args.(0), Pr.get_ival args.(1) with
  | (Pr.Iv_int x, Pr.Iv_int y) -> if x <> y then
    (* failwith "Found toplevel conflict in int_eq." *)
    raise Pr.Root_failure
  | ( Pr.Iv_var x, Pr.Iv_int k
    | Pr.Iv_int k, Pr.Iv_var x) ->
      apply_idef st x (Iv_const k)
  | (Pr.Iv_var x, Pr.Iv_var y) -> apply_idef st x (Iv_eq y)

let simp_bool2int pr st args anns =
  match Pr.get_bval args.(0), Pr.get_ival args.(1) with
  | Pr.Bv_bool b, Pr.Iv_int y ->
    if b <> (y = 1) then (* failwith "Toplevel conflict in bool2int." *)
    raise Pr.Root_failure
  | Pr.Bv_var b, Pr.Iv_int y ->
    apply_bdef st b (Bv_const (y = 1))
  | Pr.Bv_bool b, Pr.Iv_var y ->
    apply_idef st y (Iv_const (if b then 1 else 0))
  | Pr.Bv_var b, Pr.Iv_var y ->
    (* apply_idef st y (Iv_b2i b) *)
    apply_bdef st b (At (y, Igt, 0))

let simp_linterms st cs xs k =
  let ts = ref [] in
  let k' = ref k in
  Array.iteri (fun i x ->
    match x with
      | Pr.Iv_var x' -> 
        begin
        (* TODO: Proper alias resolution here. *)
        match st.idefs.(x') with
        | Iv_const cx -> k' := !k' - cx * cs.(i)
        | Iv_eq x'' -> ts := (cs.(i), x'') :: !ts
        | Iv_opp x'' -> ts := (- cs.(i), x'') :: !ts
        | _ -> ts := (cs.(i), x') :: !ts
        end
      | Pr.Iv_int cx -> k' := !k' - cx * cs.(i)
    ) xs ;
  (* TODO: Combine duplicates. *)
  (* let ts' = List.sort (fun (k, x) (k', x') -> compare x x') !ts in *)
  !ts, !k'

let simp_set_in pr st args anns =
  let dom = match args.(1) with
  | Pr.Set d -> d
  | _ -> failwith "Type mismatch in set_in."
  in
  match Pr.get_ival args.(0) with
  | Pr.Iv_int k -> () (* TODO: Check domain *)
  | Pr.Iv_var x ->
    if not (Pr.dom_meet pr x dom) then
      raise Pr.Root_failure


let rebuild_lin_args ts k =
  let cs = Array.map (fun (k, x) -> Pr.Ilit k) ts in
  let xs = Array.map (fun (k, x) -> Pr.Ivar x) ts in
  [|Pr.Arr cs ; Pr.Arr xs ; Pr.Ilit k|]

let defined_var problem anns = 
  match Pr.ann_call_args anns "defines_var" with
  | Some [| v |] ->
    begin match Pr.resolve_ann  problem v with
    | Pr.Ivar v' -> Some v'
    | _ -> None
    end
  | _ -> None

let def_of_lineq x ts k =
  let rec aux ts acc =
    match ts with
    | [] -> None
    | (1, y) :: ts' when x = y -> 
      (* Negate terms *)
      let ds = List.append acc ts' |> List.map (fun (c, z) -> (-c, z)) in
      Some (Array.of_list ds, k)
    | (-1, y) :: ts' when x = y ->
      (* Negate constant *)
      let ds = List.append acc ts' in
      Some (Array.of_list ds, -k)
    | (_, y) :: _ when x = y -> None
    | t :: ts' -> aux ts' (t :: acc)
  in
  aux ts [] 
      
let simp_lin_eq pr st args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array Pr.get_ival args.(1) in
  let k = Pr.get_int args.(2) in
  let ts', k' = simp_linterms st cs xs k in
  match defined_var pr anns with
  | Some v ->
    begin
      match def_of_lineq v ts' k' with
      | Some (ds, c) -> apply_idef st v (Iv_lin (ds, c))
      | None -> 
        Dy.add st.cons (("int_lin_eq", rebuild_lin_args (Array.of_list ts') k'), anns)
    end
  | None ->
      Dy.add st.cons (("int_lin_eq", rebuild_lin_args (Array.of_list ts') k'), anns)

let simplify_constraint problem state id args anns =
  try
    let simplifier = H.find registry id in
    try
        simplifier problem state args anns
    with Pr.Root_failure ->
      let _ = Format.fprintf Format.err_formatter "%% Toplevel failure simplifying %s.@." id
      in raise Pr.Root_failure
  with Not_found -> Dy.add state.cons ((id, args), anns)

let log_reprs idefs bdefs =
  if !Opts.verbosity > 0 then
    let sub = Array.sub bdefs 0 (min 100 (Array.length bdefs - 1)) in
    Util.print_array ~post:"|]@." (fun fmt def ->
      Format.pp_print_string fmt (string_of_bdefn def)
    ) Format.std_formatter (* bdefs *) sub
    (*
    ()
    *)
  else ()

let simplify problem =
(*
  let bdefs = Array.make (Dy.length problem.Pr.bvals) None in
  (bdefs, problem)
  *)
  let state = init_state problem in
  Dy.iter
    (fun ((id, args), anns) -> simplify_constraint problem state id args anns (*; log_reprs state.idefs state.bdefs *))
    problem.Pr.constraints ;
  (* log_reprs state.idefs state.bdefs ; *)
  (state.idefs, state.bdefs, { problem with Pr.constraints = state.cons })

(* Register all the simplifiers. *)
let init () = 
  let handlers =
    [
      "int_le_reif", simp_irel_reif Ile ; 
      "int_eq_reif", simp_irel_reif Ieq ;
      "int_ne_reif", simp_irel_reif Ine ;
      "int_lin_eq", simp_lin_eq ;
      "int_eq", simp_int_eq ;
      "bool_eq", simp_bool_eq ; 
      "bool_not", simp_bool_ne ;
      "bool2int", simp_bool2int ;
      "set_in", simp_set_in ;
    ] in
  List.iter (fun (id, h) -> H.add registry id h) handlers

let _ = init ()
