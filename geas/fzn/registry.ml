(** Constraint registry *)
module H = Hashtbl
module Pr = Problem

module At = Atom
module B = Builtins
module S = Solver

type env = { ivars : Solver.intvar array ; bvars : Atom.atom array }
type expr = (Solver.intvar, Atom.t) Problem.expr

type poster = Solver.t -> expr array -> Problem.ann_expr list -> bool
type raw_poster = Solver.t -> env -> Problem.fzn_expr array -> Problem.ann_expr list -> bool

let registry = H.create 17

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

let lift_poster (p : poster) : raw_poster =
  fun solver env args anns ->
    let res_args = Array.map (resolve_expr env) args in
    p solver res_args anns
  
let register ident poster = H.add registry ident (lift_poster poster)
let register_raw ident (poster : raw_poster) = H.add registry ident poster


let lookup ident = H.find registry ident

let bool_atom b = if b then Atom.at_True else Atom.neg Atom.at_True

let array_nth expr i =
  match expr with
  | Pr.Arr es -> es.(i)
  | _ -> failwith "Expected array argument to array_nth"

let get_atom expr =
  match Pr.get_bval expr with
  | Pr.Bv_bool b -> bool_atom b
  | Pr.Bv_var at -> at

(* Is an expression an array with a given property? *)
let is_array p expr =
  match expr with
  | Pr.Arr es -> Array.fold_left (fun b x -> b && p x) true es
  | _ -> false
let is_int expr =
  match expr with
  | Pr.Ilit k -> true
  | _ -> false
let is_bool expr =
  match expr with
  | Pr.Blit b -> true
  | _ -> false

let force_ivar solver expr =
  match expr with
  | Pr.Ilit x -> S.new_intvar solver x x
  | Pr.Ivar v -> v
  | _ -> failwith "Expected int-sorted value."

let ignore_constraint _ _ _ = true

(* Helper functions *)
let post_clauses s cs =
  let rec aux cs =
    match cs with
    | [] -> true
    | c :: cs' -> if S.post_clause s c then aux cs' else false
  in aux cs

 let bool_iff solver x y =
  S.post_clause solver [|x ; At.neg y|]
  && S.post_clause solver [|At.neg x ; y|]

let bool_clause solver args anns =
  let pos = Pr.get_array get_atom args.(0) in
  let neg = Pr.get_array (fun x -> Atom.neg (get_atom x)) args.(1) in
  Solver.post_clause solver (Array.append pos neg)

let int_max solver args anns =
  let x = force_ivar solver args.(0) in
  let y = force_ivar solver args.(1) in
  let z = force_ivar solver args.(2) in
  Builtins.int_max solver At.at_True z [|x; y|]

let int_min solver args anns =
  let x = force_ivar solver args.(0) in
  let y = force_ivar solver args.(1) in
  let z = force_ivar solver args.(2) in
  Builtins.int_max solver At.at_True
    (Solver.intvar_neg z)
    [|Solver.intvar_neg x; Solver.intvar_neg y|]

let array_int_max solver args anns =
  let xs = Pr.get_array (force_ivar solver) args.(1) in
  let z = force_ivar solver args.(0) in
  Builtins.int_max solver At.at_True z xs

let array_int_min solver args anns =
  let xs = Pr.get_array (force_ivar solver) args.(1) in
  let z = force_ivar solver args.(0) in
  Builtins.int_max solver At.at_True (Solver.intvar_neg z) (Array.map Solver.intvar_neg xs)

let int_mul solver args anns =
  let x = force_ivar solver args.(0) in
  let y = force_ivar solver args.(1) in
  let z = force_ivar solver args.(2) in
  Builtins.int_mul solver At.at_True z x y

let int_div solver args anns =
  let x = force_ivar solver args.(0) in
  let y = force_ivar solver args.(1) in
  let z = force_ivar solver args.(2) in
  Builtins.int_div solver At.at_True z x y

(* TODO: Should really be keeping rs as an identifier, to
 * be resolved only when needed. *)
let get_table =
  let t = H.create 17 in
  fun s len rs ->
    try H.find t (S.solver_id s, rs)
    with Not_found ->
      begin
        let t_id = Builtins.build_table s len rs in
        H.add t (S.solver_id s, rs) t_id ;
        t_id
      end
    
let table_int solver env exprs anns =
  let args = Array.map (resolve_expr env) exprs in
  let xs = Pr.get_array (force_ivar solver) args.(0) in
  let rs = Pr.get_array Pr.get_int args.(1) in
  (* let t_id = Builtins.build_table solver (Array.length xs) rs in *)
  let t_id = get_table solver (Array.length xs) rs in
  Builtins.table solver t_id xs Builtins.Table_CT

(* Specialization of linear inequalities *)
let simplify_linterms terms k =
  let rec aux acc k' ts =
    match ts with
    | [] -> (List.rev acc), k' 
    | (0, _) :: ts' -> aux acc k' ts'
    | (c, Pr.Ilit x) :: ts' -> aux acc (k' - c*x)  ts'
    | (c, Pr.Ivar v) :: ts' -> aux ((c, v) :: acc) k' ts'
    | _ -> failwith "Expected integer-typed operands to linear."
  in
  aux [] k (Array.to_list terms)

let simplify_bool_linterms terms k =
  let rec aux acc k' ts =
    match ts with
    | [] -> (List.rev acc), k' 
    | (0, _) :: ts' -> aux acc k' ts'
    | (c, Pr.Blit false) :: ts' -> aux acc k'  ts'
    | (c, Pr.Blit true) :: ts' -> aux acc (k' - c)  ts'
    | (c, Pr.Bvar v) :: ts' -> aux ((c, v) :: acc) k' ts'
    | _ -> failwith "Expected bool-typed operands to bool-linear."
  in
  aux [] k (Array.to_list terms)

let booleanize_linterms xs k =
  let rec aux xs k acc =
    match xs with
    | [] -> Some (List.rev acc, k)
    | (c, x) :: xs' ->
      begin
        let l = S.ivar_lb x in
        let u = S.ivar_ub x in
        match u - l with
        | 0 -> aux xs' (k - c * l) acc
        | 1 ->
           begin
             if c < 0 then
               aux xs' (k - c * u) ((-c, S.ivar_lt x u) :: acc)
             else
               aux xs' (k - c * l) ((c, S.ivar_gt x l) :: acc)
           end
        | _ -> None
      end
    in
    aux xs k []

(* Specialized int_lin_le *)
let post_lin_le s r cs xs k =
  let terms = Array.init (Array.length xs) (fun i -> cs.(i), xs.(i)) in
  match simplify_linterms terms k with
  | [], k ->
    if 0 <= k then
      true
    else
      S.post_atom s (At.neg r)
  | [c, x], k ->
    if c < 0 then
      S.post_clause s [|At.neg r; S.ivar_ge x (Util.div_ceil (-k) (-c))|]
    else
      S.post_clause s [|At.neg r; S.ivar_le x (Util.div_floor k c)|]
  | [1, x; -1, y], k | [-1, y; 1, x], k -> B.int_le s r x y k
  | ts, k ->
    begin
      match booleanize_linterms ts k with
      | Some (ts', k') ->
        let zero = S.new_intvar s 0 0 in
        B.bool_linear_ge s r zero (Array.of_list ts') (- k')
      | None -> B.linear_le s r (Array.of_list ts) k
    end

(* Specialized bool_lin_le *)
(*
let post_bool_lin_le solver cs xs k =
   let terms = Array.init (Array.length xs) (fun i -> cs.(i), xs.(i)) in
  match simplify_bool_linterms terms k with
  (*
  | [], k -> 0 <= k
    (* GKG: Check for rounding *)
  | [c, x], k ->
    if c < 0 then
      S.post_atom solver (S.ivar_ge x ((-k)/(-c)))
    else
      S.post_atom solver (S.ivar_le x (k/c))
  | [1, x; -1, y], k | [-1, y; 1, x], k ->
    B.int_le solver At.at_True x y k
    *)
  | ts, k ->
    B.bool_linear_le solver At.at_True (Array.of_list ts) k

let bool_lin_le solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  post_bool_lin_le solver cs xs k
  *)

let post_lin_eq s r cs xs k =
  post_lin_le s r cs xs k
  && post_lin_le s r (Array.map ((-) 0) cs) xs (-k)

let int_lin_le solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  post_lin_le solver At.at_True cs xs k

let int_lin_le_reif s args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  match args.(3) with
  | Pr.Blit true -> post_lin_le s At.at_True cs xs k
  | Pr.Blit false -> post_lin_le s At.at_True (Array.map ((-) 0) cs) xs (-k-1)
  | Pr.Bvar r ->
    post_lin_le s r cs xs k
    && post_lin_le s (At.neg r) (Array.map ((-) 0) cs) xs (-k-1)
  | _ -> failwith "Expected bool-sorted value as reif-var." 

let get_HR_var x s =
  match x, s with
  | Pr.Blit b, Pr.Blit s -> Pr.Bv_bool (b = s)
  | Pr.Bvar b, Pr.Blit true -> Pr.Bv_var b
  | Pr.Bvar b, Pr.Blit false -> Pr.Bv_var (At.neg b)
  | _, _ -> failwith "Invalid HR args."

let int_lin_le_HR s args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  match get_HR_var args.(3) args.(4) with
  | Pr.Bv_bool true -> post_lin_le s At.at_True cs xs k
  | Pr.Bv_bool false -> true
  | Pr.Bv_var r -> post_lin_le s r cs xs k

let int_lin_le_imp s args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  match Pr.get_bval args.(3) with
  | Pr.Bv_bool true -> post_lin_le s At.at_True cs xs k
  | Pr.Bv_bool false -> true
  | Pr.Bv_var r -> post_lin_le s r cs xs k

(* r -> sum c_i x_i != k. *)
let post_lin_ne s r cs xs k =
  let terms = Array.init (Array.length xs) (fun i -> cs.(i), xs.(i)) in
  match simplify_linterms terms k with
  | [], k ->
    if 0 = k then
      S.post_atom s (At.neg r)
    else true
  | [c, x], k ->
    if k mod c = 0 then
      S.post_clause s [|At.neg r; S.ivar_ne x (k/c)|]
    else
      true
  | ts, k ->
    B.linear_ne s r (Array.of_list ts) k


let int_lin_eq solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  post_lin_eq solver At.at_True cs xs k

let int_lin_ne solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  post_lin_ne solver At.at_True cs xs k

let int_lin_eq_reif solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  match args.(3) with
  | Pr.Blit true -> post_lin_eq solver At.at_True cs xs k
  | Pr.Blit false -> post_lin_ne solver At.at_True cs xs k
  | Pr.Bvar r ->
    post_lin_eq solver r cs xs k
    && post_lin_ne solver (At.neg r) cs xs k
  | _ -> failwith "Expected bool-sorted value for reif-var."

let int_lin_ne_reif solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  match args.(3) with
  | Pr.Blit true -> post_lin_ne solver At.at_True cs xs k
  | Pr.Blit false -> post_lin_eq solver At.at_True cs xs k
  | Pr.Bvar r ->
    post_lin_ne solver r cs xs k
    && post_lin_eq solver (At.neg r) cs xs k
  | _ -> failwith "Expected bool-sorted value for reif-var."

let int_lin_ne_HR solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (fun x -> x) args.(1) in
  let k = Pr.get_int args.(2) in
  match args.(3) with
  | Pr.Blit true -> post_lin_ne solver At.at_True cs xs k
  | Pr.Blit false -> true
  | Pr.Bvar r -> post_lin_ne solver r cs xs k
  | _ -> failwith "Expected bool-sorted value for reif-var."

let bool2int solver args anns =
  let b = Pr.get_bvar args.(0) in
  let x = Pr.get_ivar args.(1) in
  (S.post_clause solver [|b ; S.ivar_le x 0|] &&
     S.post_clause solver [|At.neg b ; S.ivar_ge x 1|])
   
(* (x_1 /\ ... /\ x_n) <-> z *)
let array_bool_and solver args anns =
  let xs = Pr.get_array get_atom args.(0) in
  let z = get_atom args.(1) in
  Array.fold_left
    (fun b x -> b && S.post_clause solver [|At.neg z; x|])
    (S.post_clause solver
                   (Array.append [|z|] (Array.map At.neg xs))) xs

let array_bool_or solver args anns =
  let xs = Pr.get_array get_atom args.(0) in
  let z = get_atom args.(1) in
  Array.fold_left
    (* ~z -> ~x *)
    (fun b x -> b && S.post_clause solver [|z; At.neg x|])
    (* z -> x_1 \/ ... \/ x_n *)
    (S.post_clause solver (Array.append [|At.neg z|] xs)) xs

let val_indices ys x =
  let (_, idxs) = 
    Array.fold_left (fun (i, is) y ->
      (i+1, if x = y then i :: is else is)) (1, []) ys
  in idxs

let array_int_element solver args anns =
  let elts = Pr.get_array Pr.get_int args.(1) in
  match Pr.get_ival args.(0), Pr.get_ival args.(2) with
  | Pr.Iv_int idx, Pr.Iv_int res ->
    res = elts.(idx-1)
  | Pr.Iv_var idx, Pr.Iv_int res ->
    S.make_sparse idx (Array.of_list (val_indices elts res))
  | Pr.Iv_int idx, Pr.Iv_var res ->
    S.post_atom solver (S.ivar_eq res elts.(idx-1))
  | Pr.Iv_var idx, Pr.Iv_var res ->
    B.int_element solver At.at_True res idx elts

let all_different_int solver args anns =
  let xs = Pr.get_array (force_ivar solver) args.(0) in
  B.all_different_int solver xs

let all_different_except_0 solver args anns =
  let xs = Pr.get_array (force_ivar solver) args.(0) in
  B.all_different_except_0 solver xs

let global_card solver args anns =
  let xs = Pr.get_array (force_ivar solver) args.(0) in
  let vals = Pr.get_array Pr.get_int args.(1) in
  let count = Pr.get_array Pr.get_int args.(2) in
  (* Check counts match up *)
  let val_count = Array.fold_left (+) 0 count in
  if val_count <> Array.length xs then
    failwith "ERROR: global_card does not yet handle flexibility."
  else
    begin
      let srcs = Array.map (fun _ -> 1) xs in
      (* Construct the flows *)
      let var_flows = Array.init (Array.length xs) (fun i ->
        Array.init (Array.length vals) (fun j ->
          (S.ivar_eq xs.(i) vals.(j), i, j)
        )
      ) in
      B.bipartite_flow solver srcs count (Array.to_list var_flows |> Array.concat)
    end

let cumulative solver args anns =
  let xs = Pr.get_array (force_ivar solver) args.(0) in
  let dur = Pr.get_array Pr.get_int args.(1) in
  let res = Pr.get_array Pr.get_int args.(2) in
  let cap = Pr.get_int args.(3) in
  let ts = Array.init (Array.length xs) (fun ii ->
    xs.(ii), dur.(ii), res.(ii)
  ) in
  B.cumulative solver ts cap

let cumulative_var solver args anns =
  let xs = Pr.get_array (force_ivar solver) args.(0) in
  let dur = Pr.get_array (force_ivar solver) args.(1) in
  let res = Pr.get_array (force_ivar solver) args.(2) in
  let cap = force_ivar solver args.(3) in
  let ts = Array.init (Array.length xs) (fun ii ->
    xs.(ii), dur.(ii), res.(ii)
  ) in
  B.cumulative_var solver ts cap

let disjunctive s args anns =
  let xs = Pr.get_array (force_ivar s) args.(0) in
  let dur = Pr.get_array Pr.get_int args.(1) in
  let ts = Array.init (Array.length xs) (fun ii -> xs.(ii), dur.(ii)) in
  B.disjunctive s ts

let array_var_int_element solver args anns =
  match Pr.get_ival args.(0), Pr.get_ival args.(2) with
  | Pr.Iv_int idx, Pr.Iv_int res ->
    begin
      match Pr.get_ival (array_nth args.(1) (idx-1)) with
      | Pr.Iv_int elt -> res = elt
      | Pr.Iv_var elt -> S.post_atom solver (S.ivar_eq elt res)
    end
  | Pr.Iv_int idx, Pr.Iv_var res -> 
    begin
      match Pr.get_ival (array_nth args.(1) (idx-1)) with
      | Pr.Iv_int elt -> S.post_atom solver (S.ivar_eq res elt)
      | Pr.Iv_var elt ->
        B.int_le solver At.at_True res elt 0
          && B.int_le solver At.at_True elt res 0
    end
  | Pr.Iv_var idx, Pr.Iv_int res ->
    Util.array_everyi 
      (fun i elt ->
        match Pr.get_ival elt with
        | Pr.Iv_int k ->
          if res = k then
            true
          else
            S.post_atom solver (S.ivar_ne idx (i+1))
        | Pr.Iv_var v ->
          S.post_clause solver [|S.ivar_ne idx (i+1) ; S.ivar_eq v res|]
        ) (Pr.get_array (fun x -> x) args.(1))
  | Pr.Iv_var idx, Pr.Iv_var res ->
    if is_array is_int args.(1) then
      let elts = Pr.get_array Pr.get_int args.(1) in
      B.int_element solver At.at_True res idx elts
    else 
      let elts = Pr.get_array (force_ivar solver) args.(1) in
      B.var_int_element solver At.at_True res idx elts

let atom_iff at b = if b then at else (At.neg at)

let array_bool_element solver args anns =
  let elts = Pr.get_array Pr.get_bool args.(1) in
  match Pr.get_ival args.(0), Pr.get_bval args.(2) with
  | Pr.Iv_int idx, Pr.Bv_bool b -> elts.(idx-1) = b
  | Pr.Iv_int idx, Pr.Bv_var at -> S.post_atom solver (atom_iff at elts.(idx-1))
  | Pr.Iv_var idx, Pr.Bv_bool b ->
    Util.array_everyi (fun i b' ->
      if b = b' then
        true
      else S.post_atom solver (S.ivar_ne idx (i+1))) elts 
  | Pr.Iv_var idx, Pr.Bv_var at ->
    Util.array_everyi (fun i b ->
      S.post_clause solver [| S.ivar_ne idx (i+1) ; atom_iff at b |]) elts
     
let array_var_bool_element solver args anns =
  match Pr.get_ival args.(0), Pr.get_bval args.(2) with
  | Pr.Iv_int idx, Pr.Bv_bool b ->
    begin
      match Pr.get_bval (array_nth args.(1) (idx-1)) with
      | Pr.Bv_bool b' -> b = b'
      | Pr.Bv_var at -> S.post_atom solver (atom_iff at b)
    end
  | Pr.Iv_int idx, Pr.Bv_var at -> 
    begin
      match Pr.get_bval (array_nth args.(1) (idx-1)) with
      | Pr.Bv_bool b -> S.post_atom solver (atom_iff at b)
      | Pr.Bv_var at' ->
        post_clauses solver
          [ [|at; At.neg at'|] ;
            [|At.neg at; at'|] ]
    end
  | Pr.Iv_var idx, Pr.Bv_bool b ->
    Util.array_everyi (fun i elt ->
        match Pr.get_bval elt with
        | Pr.Bv_bool b' ->
          if b = b' then
            true
          else
            S.post_atom solver (S.ivar_ne idx (i+1))
        | Pr.Bv_var at ->
          S.post_clause solver [|S.ivar_ne idx (i+1) ; atom_iff at b|]
    ) (Pr.get_array (fun x -> x) args.(1))
  | Pr.Iv_var idx, Pr.Bv_var at ->
    if is_array is_bool args.(1) then
      let elts = Pr.get_array Pr.get_bool args.(1) in
      Util.array_everyi (fun i b ->
          S.post_clause solver [|S.ivar_ne idx (i+1) ; atom_iff at b|]
      ) elts
    else 
      let elts = Pr.get_array get_atom args.(1) in
      Util.array_everyi (fun i at' ->
          let ne = S.ivar_ne idx (i+1) in
          post_clauses solver
            [ [| ne; at; At.neg at' |] ;
              [| ne; At.neg at; at' |] ]) elts

let int_eq solver args anns =
  match args.(0), args.(1) with
  | Pr.Ivar x, Pr.Ivar y ->
    B.int_le solver At.at_True x y 0 && B.int_le solver At.at_True y x 0
  | Pr.Ilit c, Pr.Ivar x | Pr.Ivar x, Pr.Ilit c ->
    S.post_atom solver (S.ivar_le x c) && S.post_atom solver (S.ivar_ge x c)
  | Pr.Ilit c1, Pr.Ilit c2 -> c1 = c2
  | _, _ -> failwith "int_eq expects int operands."

(* x <= y + k *)
let post_int_diff s r x y k =
  match x, y with
  | Pr.Ivar x, Pr.Ivar y -> B.int_le s r x y k
  | Pr.Ivar x, Pr.Ilit c -> S.post_clause s [|At.neg r; S.ivar_le x (c+k)|]
  | Pr.Ilit c, Pr.Ivar y -> S.post_clause s [|At.neg r; S.ivar_ge y (c-k)|]
  | Pr.Ilit c1, Pr.Ilit c2 ->
     ((* Format.fprintf Format.err_formatter "{r} -> %d <= %d + %d@." c1 c2 k ; *)
    if c1 > c2 + k then
      S.post_atom s (At.neg r)
    else true)
  | _, _ -> failwith "Expected int-sorted arguments to int relation."

let int_le solver args anns =
  post_int_diff solver At.at_True args.(0) args.(1) 0
let int_lt solver args anns =
  post_int_diff solver At.at_True args.(0) args.(1) (-1)

let int_le_reif solver args anns =
  match args.(2) with
  | Pr.Blit true -> post_int_diff solver At.at_True args.(0) args.(1) 0 
  | Pr.Blit false -> post_int_diff solver At.at_True args.(1) args.(0) (-1)
  | Pr.Bvar r ->
    post_int_diff solver r args.(0) args.(1) 0
    && post_int_diff solver (At.neg r) args.(1) args.(0) (-1)
  | _ -> failwith "Expected bool-typed reif var"

let int_le_HR solver args anns =
  match get_HR_var args.(2) args.(3) with
  | Pr.Bv_bool true -> post_int_diff solver At.at_True args.(0) args.(1) 0 
  | Pr.Bv_bool false -> true
  | Pr.Bv_var r -> post_int_diff solver r args.(0) args.(1) 0

let int_le_imp solver args anns =
  match Pr.get_bval args.(2) with
  | Pr.Bv_bool true -> post_int_diff solver At.at_True args.(0) args.(1) 0 
  | Pr.Bv_bool false -> true
  | Pr.Bv_var r -> post_int_diff solver r args.(0) args.(1) 0

let int_lt_reif solver args anns =
  match args.(2) with
  | Pr.Blit true -> post_int_diff solver At.at_True args.(0) args.(1) (-1) 
  | Pr.Blit false -> post_int_diff solver At.at_True args.(1) args.(0) 0
  | Pr.Bvar r ->
    post_int_diff solver r args.(0) args.(1) (-1)
    && post_int_diff solver (At.neg r) args.(1) args.(0) 0
  | _ -> failwith "Expected bool-typed reif var"

let int_lt_HR solver args anns =
  match get_HR_var args.(2) args.(3) with
  | Pr.Bv_bool true -> post_int_diff solver At.at_True args.(0) args.(1) (-1) 
  | Pr.Bv_bool false -> false
  | Pr.Bv_var r -> post_int_diff solver r args.(0) args.(1) (-1)

let int_ne solver args anns =
  match Pr.get_ival args.(0), Pr.get_ival args.(1) with
  | Pr.Iv_int k1, Pr.Iv_int k2 -> k1 <> k2
  | (Pr.Iv_var x, Pr.Iv_int k)
  | (Pr.Iv_int k, Pr.Iv_var x) -> S.post_atom solver (S.ivar_ne x k)
  | Pr.Iv_var x, Pr.Iv_var y -> B.int_ne solver At.at_True x y

let int_eq_reif solver args anns =
  match Pr.get_bval args.(2) with
  | Pr.Bv_bool true -> int_eq solver args anns
  | Pr.Bv_bool false -> int_ne solver args anns
  | Pr.Bv_var r ->
  begin
    match Pr.get_ival args.(0), Pr.get_ival args.(1) with
    | Pr.Iv_int k1, Pr.Iv_int k2 ->
      if k1 = k2 then
        S.post_atom solver r
      else
        S.post_atom solver (At.neg r)
    | (Pr.Iv_var x, Pr.Iv_int k)
    | (Pr.Iv_int k, Pr.Iv_var x) ->
      let at = S.ivar_eq x k in
      bool_iff solver r at
    | Pr.Iv_var x, Pr.Iv_var y ->
    (* *)
      B.int_le solver r x y 0
      && B.int_le solver r y x 0
      (* )
      B.int_eq solver r x y
      ( *)
      && B.int_ne solver (At.neg r) x y
  end

let int_eq_HR solver args anns =
  match get_HR_var args.(2) args.(3) with
  | Pr.Bv_bool true -> int_eq solver args anns
  | Pr.Bv_bool false -> true
  | Pr.Bv_var r ->
  begin
    match Pr.get_ival args.(0), Pr.get_ival args.(1) with
    | Pr.Iv_int k1, Pr.Iv_int k2 -> 
      if k1 = k2 then true else S.post_atom solver (At.neg r)
    | (Pr.Iv_var x, Pr.Iv_int k)
    | (Pr.Iv_int k, Pr.Iv_var x) ->
      let at = S.ivar_eq x k in
      S.post_clause solver [|At.neg r ; at |]
    | Pr.Iv_var x, Pr.Iv_var y ->
      B.int_le solver r x y 0
      && B.int_le solver r y x 0
  end

let int_eq_imp solver args anns =
  match Pr.get_bval args.(2) with
  | Pr.Bv_bool true -> int_eq solver args anns
  | Pr.Bv_bool false -> true
  | Pr.Bv_var r ->
  begin
    match Pr.get_ival args.(0), Pr.get_ival args.(1) with
    | Pr.Iv_int k1, Pr.Iv_int k2 -> 
      if k1 = k2 then true else S.post_atom solver (At.neg r)
    | (Pr.Iv_var x, Pr.Iv_int k)
    | (Pr.Iv_int k, Pr.Iv_var x) ->
      let at = S.ivar_eq x k in
      S.post_clause solver [|At.neg r ; at |]
    | Pr.Iv_var x, Pr.Iv_var y ->
      B.int_le solver r x y 0
      && B.int_le solver r y x 0
  end

let int_ne_reif solver args anns =
  match Pr.get_bval args.(2) with
  | Pr.Bv_bool true -> int_ne solver args anns
  | Pr.Bv_bool false -> int_eq solver args anns
  | Pr.Bv_var r ->
  begin
    match Pr.get_ival args.(0), Pr.get_ival args.(1) with
    | Pr.Iv_int k1, Pr.Iv_int k2 ->
      if k1 = k2 then
        S.post_atom solver (At.neg r)
      else
        S.post_atom solver r
    | (Pr.Iv_var x, Pr.Iv_int k)
    | (Pr.Iv_int k, Pr.Iv_var x) ->
      let at = S.ivar_ne x k in
      bool_iff solver r at
    | Pr.Iv_var x, Pr.Iv_var y ->
      B.int_ne solver r x y
      (*
      && B.int_le solver (At.neg r) x y 0
      && B.int_le solver (At.neg r) y x 0
      *)
      && B.int_eq solver (At.neg r) x y
  end

let int_ne_HR solver args anns =
  match get_HR_var args.(2) args.(3) with
  | Pr.Bv_bool true -> int_ne solver args anns
  | Pr.Bv_bool false -> true
  | Pr.Bv_var r ->
  begin
    match Pr.get_ival args.(0), Pr.get_ival args.(1) with
    | Pr.Iv_int k1, Pr.Iv_int k2 ->
      if k1 = k2 then
        S.post_atom solver (At.neg r)
      else
        true
    | (Pr.Iv_var x, Pr.Iv_int k)
    | (Pr.Iv_int k, Pr.Iv_var x) ->
      let at = S.ivar_ne x k in
      S.post_clause solver [|At.neg r ; at |]
    | Pr.Iv_var x, Pr.Iv_var y ->
      B.int_ne solver r x y
  end

let int_ne_imp solver args anns =
  match Pr.get_bval args.(2) with
  | Pr.Bv_bool true -> int_ne solver args anns
  | Pr.Bv_bool false -> true
  | Pr.Bv_var r ->
  begin
    match Pr.get_ival args.(0), Pr.get_ival args.(1) with
    | Pr.Iv_int k1, Pr.Iv_int k2 ->
      if k1 = k2 then
        S.post_atom solver (At.neg r)
      else
        true
    | (Pr.Iv_var x, Pr.Iv_int k)
    | (Pr.Iv_int k, Pr.Iv_var x) ->
      let at = S.ivar_ne x k in
      S.post_clause solver [|At.neg r ; at |]
    | Pr.Iv_var x, Pr.Iv_var y ->
      B.int_ne solver r x y
  end

let int_abs solver args anns =
  match Pr.get_ival args.(0), Pr.get_ival args.(1) with
  | Pr.Iv_int x, Pr.Iv_int z -> z = abs x
  | Pr.Iv_var x, Pr.Iv_int z -> S.make_sparse x [|-z ; z|]
  | Pr.Iv_int k, Pr.Iv_var x -> S.post_atom solver (S.ivar_eq x (abs k))
  | Pr.Iv_var x, Pr.Iv_var z -> B.int_abs solver At.at_True z x

let bool_eq solver args anns =
  match Pr.get_bval args.(0), Pr.get_bval args.(1) with
  | Pr.Bv_bool a, Pr.Bv_bool b -> a = b
  | (Pr.Bv_bool b, Pr.Bv_var x)
  | (Pr.Bv_var x, Pr.Bv_bool b) ->
    if b then
      S.post_atom solver x
    else
      S.post_atom solver (At.neg x)
  | Pr.Bv_var x, Pr.Bv_var y ->
    S.post_clause solver [|x ; At.neg y|]
    && S.post_clause solver [|At.neg x ; y |]

let bool_eq_reif solver args anns =
  let z = get_atom args.(2) in
  let x = get_atom args.(0) in
  let y = get_atom args.(1) in
  post_clauses solver
    [ [| At.neg z; x; At.neg y |] ;
      [| At.neg z; At.neg x; y |] ;
      [| z; x; y |] ;
      [| z; At.neg x; At.neg y |] ] 

(* z <-> ~x /\ y *)
let bool_lt_reif solver args anns =
  let z = get_atom args.(2) in
  let x = get_atom args.(0) in
  let y = get_atom args.(1) in
  post_clauses solver
    [ [| At.neg z; At.neg x |] ;
      [| At.neg z; y |] ;
      [| z ; x ; At.neg y |] ]

(* z <-> ~x \/ y *)
let bool_le_reif solver args anns =
  let z = get_atom args.(2) in
  let x = get_atom args.(0) in
  let y = get_atom args.(1) in
  post_clauses solver
    [ [| At.neg z; At.neg x; y |] ;
      [| z ; At.neg y |] ;
      [| z ; x |] ]

let atmost_one solver args anns =
  let xs = Pr.get_array get_atom args.(0) in
  B.atmost_1 solver At.at_True xs
let atmost_k solver args anns =
  let xs = Pr.get_array get_atom args.(0) in
  let k = Pr.get_int args.(1) in
  B.atmost_k solver At.at_True xs k

let precede_chain_int solver args anns =
  let xs = Pr.get_array (force_ivar solver) args.(0) in
  B.precede_chain_int solver xs

let precede_int solver args anns =
  let s = Pr.get_int args.(0) in
  let t = Pr.get_int args.(1) in
  let xs = Pr.get_array (force_ivar solver) args.(2) in
  B.precede_int solver s t xs

let value_precede_chain solver args anns =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array (force_ivar solver) args.(1) in
  let zs = Array.map (fun x -> S.permute_intvar solver x cs) xs in
  B.precede_chain_int solver zs

let bool_linear_ge solver args anns =
  let z = force_ivar solver args.(0) in
  let cs = Pr.get_array Pr.get_int args.(1) in
  let xs = Pr.get_array get_atom args.(2) in
  let k = Pr.get_int args.(3) in
  B.bool_linear_ge solver (At.at_True) z (Array.mapi (fun i x -> cs.(i), x) xs) k

let bool_linear_le solver args anns =
  let z = force_ivar solver args.(0) in
  let cs = Pr.get_array Pr.get_int args.(1) in
  let xs = Pr.get_array get_atom args.(2) in
  let k = Pr.get_int args.(3) in
  B.bool_linear_le solver (At.at_True) z (Array.mapi (fun i x -> cs.(i), x) xs) k

(* Maybe separate this out into a separate
 * per-solver registrar *)
let initialize () =
  let handlers =
    ["bool_clause", bool_clause ;
     "int_max", int_max ;
     "int_min", int_min ;
     "array_int_maximum", array_int_max ;
     "array_int_minimum", array_int_min ;
     "int_times", int_mul ;
     "int_div", int_div ;
     "int_lin_le", int_lin_le ;
     "int_lin_le_reif", int_lin_le_reif ;
     "int_lin_le_HR", int_lin_le_HR ;
     "int_lin_le_imp", int_lin_le_imp ;
     "int_lin_eq", int_lin_eq ;
     "int_lin_eq_reif", int_lin_eq_reif ;
     "int_lin_ne", int_lin_ne ;
     "int_lin_ne_reif", int_lin_ne_reif ;
     "int_lin_ne_HR", int_lin_ne_HR ;
     "int_eq", int_eq ;
     "int_ne", int_ne ;
     "int_le", int_le ;
     "int_le_reif", int_le_reif ;
     "int_le_HR", int_le_HR ;
     "int_le_imp", int_le_imp ;
     "int_lt", int_lt ;
     "int_lt_reif", int_lt_reif ;
     "int_lt_HR", int_lt_HR ;
     "int_abs", int_abs ;
     "int_eq_reif", int_eq_reif ;
     "int_eq_HR", int_eq_HR ;
     "int_eq_imp", int_eq_imp ;
     "int_ne_reif", int_ne_reif ;
     "int_ne_HR", int_ne_HR ;
     "int_ne_imp", int_ne_imp ;
     "bool2int", bool2int ;
     "bool_eq", bool_eq ;
     "bool_eq_reif", bool_eq_reif ;
     "bool_lt_reif", bool_lt_reif ;
     "bool_le_reif", bool_le_reif ;
     "array_bool_and", array_bool_and ;
     "array_bool_or", array_bool_or ;
     (* "bool_sum_le", bool_sum_le ; *)
     "bool_lin_ge", bool_linear_ge ;
     "bool_lin_le", bool_linear_le ;
     "atmost_one", atmost_one ;
     "atmost_k", atmost_k ;
     "array_int_element", array_int_element ; 
     "array_var_int_element", array_var_int_element ;
     "array_bool_element", array_bool_element ;
     "array_var_bool_element", array_var_bool_element ;
     (* "bool_lin_le", bool_lin_le ; *)
     "fzn_all_different_int", all_different_int ;
     "geas_all_different_int", all_different_int ;
     "fzn_all_different_except_0", all_different_except_0 ;
     "fzn_cumulative", cumulative ;
     "fzn_cumulative_var", cumulative_var ;
     "fzn_disjunctive", disjunctive ;
     "geas_disjunctive", disjunctive ;
     "fzn_global_cardinality", global_card ;
     "geas_all_different_int", all_different_int ;
     "geas_all_different_except_0", all_different_except_0 ;
     "geas_cumulative", cumulative ;
     "geas_cumulative_var", cumulative_var ;
     "geas_disjunctive", disjunctive ;
     "geas_global_cardinality", global_card ;
     "value_precede_int", precede_int ;
     "geas_precede_chain", precede_chain_int ;
     "geas_value_precede_chain", value_precede_chain ;
      ] in
  let raw_handlers = [
     "fzn_table_int", table_int ;
     "geas_table_int", table_int 
  ] in
  List.iter (fun (id, handler) ->
             register id handler) handlers ;
  List.iter (fun (id, handler) ->
             register_raw id handler) raw_handlers
