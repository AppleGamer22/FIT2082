(* Dealing with systems of definitions. *)
module Dy = DynArray
module H = Hashtbl
module L = List
module A = Array
module Q = Queue

type val_id = int

type irel = Ile | Ieq | Igt | Ine

type 'a def = 
  (* Boolean functions *)
  | Bv_const of bool
  | Bv_neg of 'a
  | At of 'a * irel * int
  | Bv_or of 'a array
  | Bv_and of 'a array
  (* Integer functions *)
  | Iv_const of int
  | Iv_opp of 'a
  (* Arithmetic functions *)
  | Iv_sum of 'a array
  | Iv_prod of 'a array
  | Iv_max of 'a array
  | Iv_min of 'a array
  | Iv_b2i of 'a
  | Elem of 'a array * 'a

let def_map f def =
  match def with
  | Bv_const b -> Bv_const b
  | Bv_neg x -> Bv_neg (f x)
  | At (x, r, k) -> At (f x, r, k)
  | Bv_or xs -> Bv_or (Array.map f xs)
  | Bv_and xs -> Bv_and (Array.map f xs)
  (* Integer stuff *)
  | Iv_const k -> Iv_const k
  | Iv_opp x -> Iv_opp (f x)
  (* Arithmetic functions *)
  | Iv_sum xs -> Iv_sum (Array.map f xs)
  | Iv_prod xs -> Iv_prod (Array.map f xs)
  | Iv_max xs -> Iv_max (Array.map f xs)
  | Iv_min xs -> Iv_min (Array.map f xs)
  | Iv_b2i x -> Iv_b2i (f x)
  | Elem (ys, i) -> Elem (Array.map f ys, f i)

(* We need to keep track of:
 * - definitions
 * - occurrences. *)
type def_id = int

type var_defI =
  | AliasI of val_id
  | DefI of def_id list

type var_def =
  | Alias of val_id
  | Def of val_id def list

type t = {
  defs : var_defI array ;
  occurs: def_id list array ; 
  
  (* Specific expressions *)
  nodes : (val_id * val_id def) Dy.t ;
  node_tbl : (val_id def, val_id) H.t ;
  
  (* Bookkeeping *)
  flags : bool array ;
  queue : int Q.t ;
  queued : bool Dy.t 
}

let create sz = {
  defs = Array.create sz (DefI []) ;
  occurs = Array.create sz [] ;
  nodes = Dy.create () ;
  node_tbl = H.create 17 ;

  flags = Array.create sz false ;
  queue = Q.create () ;
  queued = Dy.create ()
}

let enqueue st d =
  if Dy.get st.queued d then
    ()
  else
    (Dy.set st.queued d true; Q.add d st.queue )

let dequeue st =
  let d = Q.pop st.queue in
  Dy.set st.queued d false ;
  d

let unique st xs =
  (* Collect the occurrences in reverse *)
  let ys = Array.fold_left
    (fun ys x ->
      if st.flags.(x) then
        ys
      else
        (st.flags.(x) <- true ; x :: ys)) [] xs in
  (* Reset flags while un-reversing *)
  List.fold_left (fun ys x -> st.flags.(x) <- false ; x :: ys) [] ys

let get_occurs st def =
  match def with
  | Bv_neg x -> [x]
  | At (x, _, _) -> [x]
  | Bv_or xs -> unique st xs
  | Bv_and xs -> unique st xs
  | Iv_opp x -> [x]
  | Iv_sum xs -> unique st xs
  | Iv_prod xs -> unique st xs
  | Iv_max xs -> unique st xs
  | Iv_min xs -> unique st xs
  | Iv_b2i x -> [x]
  | Elem (ys, i) -> unique st (A.append [|i|] ys)
  | _ -> []

let rec repr st v =
  match st.defs.(v) with
  | AliasI v' ->
    let v'' = repr st v' in
    let _ = st.defs.(v) <- AliasI v'' in
    v''
  | _ -> v

let is_canon st v =
  match st.defs.(v) with
  | DefI _ -> true
  | AliasI _ -> false


let merge_occurs st orig =
  let occ = List.fold_left (fun ys xs ->
    List.fold_left (fun ys x -> 
      if st.flags.(x) then
        ys
      else (st.flags.(x) <- true ; x :: ys)) ys xs) [] orig in
  List.fold_left (fun ys x -> st.flags.(x) <- false ; x :: ys) [] occ


let get_defs st v =
  match st.defs.(v) with
  | DefI d -> d
  | _ -> failwith "ERROR: get_defs called on non-canonical var"

let simplify st def =
  def_map (repr st) def
  (*
  match def_map (repr st) def with
  | Bv_neg x -> List.fold_left 
  | At (x, r, k) -> 
  | Bv_or xs -> Bv_or (Array.map f xs)
  | Bv_and xs -> Bv_and (Array.map f xs)
  (* Integer functions *)
  | Iv_const k -> Iv_const k
  (* Aliasing *)
  | Iv_eq x -> Iv_eq (f x)
  (* Arithmetic functions *)
  | Iv_sum xs -> Iv_sum (Array.map f xs)
  | Iv_prod xs -> Iv_prod (Array.map f xs)
  | Iv_max xs -> Iv_max (Array.map f xs)
  | Iv_min xs -> Iv_min (Array.map f xs)
  | Iv_b2i x -> Iv_b2i (f x)
  *)

let merge st v w =
  if v = w then
    ()
  else
    begin
      let v_sz = List.length st.occurs.(v) in
      let w_sz = List.length st.occurs.(w) in
      let v', w' = if v_sz >= w_sz then v, w else w, v in
      (* Pick the most frequently-occurring representative *)
      st.defs.(v') <-
        DefI (List.rev_append (get_defs st w') (get_defs st v')) ;
      st.defs.(w') <- AliasI v' ;
      List.iter (enqueue st) st.occurs.(w') ;
      st.occurs.(v') <- List.rev_append st.occurs.(w') st.occurs.(v')
    end

(* v and w should be canonical elements *)
let update_def st idx =
  let (v, def) = Dy.get st.nodes idx in
  let canon = simplify st def in
  if def <> canon then
    begin
      H.remove st.node_tbl def ;
      try
        let v' = H.find st.node_tbl canon in
        merge st v v'
      with Not_found ->
        let _ = H.add st.node_tbl canon idx in 
        Dy.set st.nodes idx (v, canon)
    end

let close st =
  while not (Q.is_empty st.queue) do
    let v = dequeue st in
    update_def st v
  done

let rec bind st v def =
  let canon = def_map (repr st) def in
  try
    let w = H.find st.node_tbl canon in
    merge st v w 
  with Not_found ->
    (* New definition *)
    begin
      let v' = repr st v in
      let idx = Dy.length st.nodes in
      H.add st.node_tbl canon v' ;
      Dy.add st.nodes (v', canon) ;
      Dy.add st.queued false ;
      (* Add the new definition *)
      st.defs.(v') <- DefI (idx :: (get_defs st v')) ;
      (* Update occurrences *)
      let occ = get_occurs st canon in
      List.iter (fun o ->
        st.occurs.(o) <- v' :: st.occurs.(o)
      ) occ ;
      List.iter (update_def st) st.occurs.(v')
    end

let equal st x y = merge st x y

let extract st =
  let get d = simplify st @@ snd @@ Dy.get st.nodes d in
  Array.map (fun def ->
    match def with
    | AliasI v -> Alias (repr st v)
    | DefI xs -> Def (List.map get xs)) st.defs
