(* Interface file for a Flatzinc problem *)
(* FIXME: Deal with annotations *)
module Dy = DynArray
module H = Hashtbl

exception Sym_error of string
exception Type_mismatch
exception Root_failure

(* Constraint items *)
type ident = string
(*
type item = ident * (fzn_expr array) 
*)

type ival_id = int
type bval_id = int

(* Just model representation -- not worrying about
 * aliasing/definitions *)
type lbool = LFalse | LUndef | LTrue

type ('iv, 'bv) expr =
  | Ilit of int
  | Ivar of 'iv
  | Blit of bool
  | Bvar of 'bv
  | Set of Dom.t
  | Arr of ('iv, 'bv) expr array
  (* | Call of ident * (expr list) *)

type 'bv bval =
  | Bv_bool of bool
  | Bv_var of 'bv
type 'iv ival =
  | Iv_int of int
  | Iv_var of 'iv
 
let get_int = function
  | Ilit k -> k
  | _ -> raise Type_mismatch

let get_bool = function
  | Blit b -> b
  | _ -> raise Type_mismatch

let get_ivar = function
  | Ivar v -> v
  | _ -> raise Type_mismatch

let get_bvar = function
  | Bvar v -> v
  | _ -> raise Type_mismatch

let get_ival = function
  | Ivar v -> Iv_var v
  | Ilit v -> Iv_int v
  | _ -> raise Type_mismatch
                     
let get_bval = function
  | Bvar v -> Bv_var v
  | Blit v -> Bv_bool v
  | _ -> raise Type_mismatch

let get_array f = function
  | Arr x -> Array.map f x
  | _ -> raise Type_mismatch

type ann_expr =
  | Ann_int of int
  | Ann_bool of bool
  | Ann_str of string
  | Ann_set of Dom.t
  | Ann_id of ident
  | Ann_arr of ann_expr array
  | Ann_call of ident * (ann_expr array)

type goal =
  | Satisfy
  | Maximize of ival_id
  | Minimize of ival_id

type fzn_expr = (ival_id, ival_id) expr

type cstr = (ident * (fzn_expr array))
type ival_info = { id : ident ; dom : Dom.t ; ann : ann_expr list }
type model = {
  symbols : (ident, fzn_expr * ann_expr list) H.t ;
  ivals : ival_info Dy.t ;
  bvals : (ident * ann_expr list) Dy.t ;
  constraints : (cstr * ann_expr list) Dy.t ;
  mutable objective : (goal * ann_expr list)
}

type t = model

let create () = {
  symbols = H.create 17 ;
  ivals = Dy.create () ;
  bvals = Dy.create () ;
  constraints = Dy.create () ;
  objective = (Satisfy, [])
}

let new_ivar m name dom ann =
  let id = Dy.length m.ivals in
  Dy.add m.ivals { id = name ; dom = dom ; ann = ann } ;
  id

let new_bvar m name ann =
  let id = Dy.length m.bvals in
  Dy.add m.bvals (name, ann) ;
  id

let dom_of model iv = (Dy.get model.ivals iv).dom

let dom_meet m iv dom =
  let info = Dy.get m.ivals iv in
  match Dom.intersect info.dom dom with
  | None -> false
  | Some d' ->
    let _ = Dy.set m.ivals iv { info with dom = d' } in
    true

let post model id args anns =
  Dy.add model.constraints ((id, args), anns)

let resolve m id =
  try
    fst @@ H.find m.symbols id
  with Not_found -> raise (Sym_error id)

let resolve_full m id =
  try
    H.find m.symbols id
  with Not_found -> raise (Sym_error id)

let bind m id expr anns =
  try
    let _ = H.find m.symbols id in
    failwith (Format.sprintf "Identifier %s already bound" id)
  with Not_found -> H.add m.symbols id (expr, anns)

(** Inspection *)
let expr_bvars expr =
  let hs = Util.HashSet.create 13 in
  let rec aux = function
    | Bvar b -> Util.HashSet.add hs b
    | Arr es -> Array.iter aux es
    | _ -> ()
  in
  aux expr ;
  Util.HashSet.elements hs

let expr_ivars expr =
  let hs = Util.HashSet.create 13 in
  let rec aux = function
    | Ivar v -> Util.HashSet.add hs v
    | Arr es -> Array.iter aux es
    | _ -> ()
  in
  aux expr ;
  Util.HashSet.elements hs

let ann_has_id ann id = List.exists ((=) (Ann_id id)) ann
let ann_has_call ann id =
  List.exists (fun ann -> match ann with
                          | Ann_call (id', _) -> id = id'
                          | _ -> false) ann

let rec ann_call_args ann id =
  let rec aux ann =
    match ann with
    | [] -> None
    | Ann_call (id', args) :: _ when id = id' -> Some args
    | _ :: ann' -> aux ann'
  in aux ann

let rec resolve_ann state = function
  | Ann_int k -> Ilit k
  | Ann_bool b -> Blit b
  | Ann_set s -> Set s
  | Ann_id id -> resolve state id
  | Ann_arr xs -> Arr (Array.map (resolve_ann state) xs)
  | _ -> failwith "Annotation has no matching expression type"

let print_set fmt ks =
  Util.print_list Format.pp_print_int ~pre:"{" ~sep:"," ~post:"}" fmt ks
  (*
  let rec aux ks = match ks with
  | [] -> ()
  | k :: ks' -> (Format.fprintf fmt ", %d" k ; aux ks')
  in
  Format.fprintf fmt "{" ;
  match ks with
  | k :: ks' -> (Format.fprintf fmt "%d" k ; aux ks')
  | [] -> () ;
  Format.fprintf fmt "}"
  *)

let print_call pp_arg fmt id args =
  Format.fprintf fmt "%s" id ;
  Util.print_array pp_arg ~pre:"(" ~sep:"," ~post:")" fmt args

let print_dom fmt = function
  | Dom.Range (l, u) -> Format.fprintf fmt "%d..%d" l u
  | Dom.Set ks -> print_set fmt ks

let rec print_ann fmt ann =
  match ann with
  | Ann_int k -> Format.fprintf fmt "%d" k
  | Ann_bool b -> Format.fprintf fmt "%s" (if b then "true" else "false")
  | Ann_str s -> Format.fprintf fmt "\"%s\"" s
  | Ann_set d -> print_dom fmt d
  | Ann_id id -> Format.fprintf fmt "%s" id
  | Ann_arr anns -> Util.print_array print_ann ~pre:"[" ~sep:"," ~post:"]" fmt anns
  | Ann_call (id, anns) -> print_call print_ann fmt id anns

let print_anns fmt xs =
  List.iter (fun ann -> Format.fprintf fmt ":: "; print_ann fmt ann) xs

let print_ivar fmt info =
  Format.fprintf fmt "var " ;
  print_dom fmt info.dom ;
  Format.fprintf fmt ": %s" info.id;
  print_anns fmt info.ann ;
  Format.fprintf fmt ";@."

let print_bvar fmt info =
  Format.fprintf fmt "var bool: %s" (fst info) ;
  print_anns fmt (snd info) ;
  Format.fprintf fmt ";@."

(* Re-inferring type of array elements *)
type kind =
  | Bool 
  | Int of Dom.t
  | Inconsistent
type inst =
  | Par
  | Var

let merge_kind x y = match x, y with
  | Bool, Bool -> Bool
  | Int dx, Int dy -> Int (Dom.union dx dy)
  | _ -> Inconsistent

let merge_inst x y = match x, y with
  | Par, Par -> Par
  | _, _ -> Var

let ty_inst model = function
  | Ilit k -> Par, Int (Dom.set [k])
  | Ivar vi -> Var, Int (Dy.get model.ivals vi).dom
  | Blit b -> Par, Bool
  | Bvar _ -> Var, Bool
  | Set _ -> failwith "Arrays of sets not supported."
  | Arr _ -> failwith "Arrays of arrays not supported."

let merge_ty_inst x y = (merge_inst (fst x) (fst y), merge_kind (snd x) (snd y))

let args_ty_inst model xs =
  Array.fold_left merge_ty_inst (ty_inst model xs.(0)) (Array.map (ty_inst model) xs)

let rec print_expr model fmt = function
  | Ilit k -> Format.fprintf fmt "%d" k
  | Ivar vi -> Format.fprintf fmt "%s" (Dy.get model.ivals vi).id
  | Blit b -> Format.fprintf fmt "%s" (if b then "true" else "false")
  | Bvar vi -> Format.fprintf fmt "%s" (fst (Dy.get model.bvals vi))
  | Set d -> print_dom fmt d
  | Arr xs -> Util.print_array (print_expr model) ~pre:"[" ~sep:"," ~post:"]" fmt xs

let print_array_decl model fmt id expr anns =
  Format.fprintf fmt "array [%d..%d] of " 1 (Array.length expr) ;
  let inst, ty = args_ty_inst model expr in
  begin
    match inst, ty with
    | Par, Bool -> Format.fprintf fmt "bool"
    | Par, Int _ -> Format.fprintf fmt "int"
    | _, Bool -> Format.fprintf fmt "var bool"
    | _, Int dom -> (Format.fprintf fmt "var " ; print_dom fmt dom)
    | _, Inconsistent -> failwith (Format.sprintf "Could not infer type of array: %s." id)
  end ;
  Format.fprintf fmt ": %s " id ;
  print_anns fmt anns ;
  Format.fprintf fmt " = ";
  Util.print_array (print_expr model) fmt ~pre:"[" ~sep:"," ~post:"];@." expr

let print_vars fmt model =
  (* Print ivars *)
  Dy.iter (print_ivar fmt) model.ivals ;
  Dy.iter (print_bvar fmt) model.bvals ;
  (* Now the remaining symbols *)
  H.iter (fun id (v, anns) ->
    match v with
    | Arr expr -> print_array_decl model fmt id expr anns
    | _ -> ()
  ) model.symbols

let print_goal fmt model =
  Format.fprintf fmt "solve";
  print_anns fmt (snd model.objective) ;
  begin
    match (fst model.objective) with
    | Satisfy -> Format.fprintf fmt " satisfy"
    | Maximize vi -> Format.fprintf fmt " maximize %s" (Dy.get model.ivals vi).id
    | Minimize vi -> Format.fprintf fmt " minimize %s" (Dy.get model.ivals vi).id 
  end;
  Format.fprintf fmt ";@."

let print_constraint fmt model ((id, args), anns) =
  Format.fprintf fmt "constraint %s" id ;
  Util.print_array (print_expr model) ~pre:"(" ~sep:"," ~post:")"  fmt args ;
  print_anns fmt anns ;
  Format.fprintf fmt ";@."

let print_constraints fmt model = Dy.iter (print_constraint fmt model) model.constraints

let print fmt model =
  print_vars fmt model ;
  print_constraints fmt model ;
  print_goal fmt model
