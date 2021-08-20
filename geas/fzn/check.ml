(* Check that a model is actually a solution. *)
module Dy = DynArray
module H = Hashtbl

module Pr = Problem
module Sol = Solver

exception Not_satisfied of string
exception No_checker of string

(* Evaluate an expression under a model.
 * - FIXME: Duplicated from fzn_phage.ml. *)
let rec eval_expr model ivars bvars expr =
  match expr with
  | Pr.Ilit v -> Pr.Ilit v
  | Pr.Ivar iv -> Pr.Ilit (Sol.int_value model ivars.(iv))
  | Pr.Blit b -> Pr.Blit b
  | Pr.Bvar bv -> Pr.Blit (Sol.atom_value model bvars.(bv))
  | Pr.Set dom -> Pr.Set dom
  | Pr.Arr es -> Pr.Arr (Array.map (eval_expr model ivars bvars) es)

let rec print_sol fmt expr =
  match expr with
  | Pr.Ilit v -> Format.pp_print_int fmt v
  | Pr.Blit b -> Format.pp_print_string fmt (if b then "true" else "false")
  | Pr.Arr es -> Util.print_array print_sol fmt es
  | _ -> ()

let checkers = H.create 17

let check prob ivars bvars model =
  try
    let _ = Dy.index_of (fun ((id, args), ann) ->
      try
        let check_fun = H.find checkers id in
        not (check_fun (Array.map (eval_expr model ivars bvars) args))
      with Not_found -> raise (No_checker id)) prob.Pr.constraints
    in false
  with Not_found -> true

let check_exn prob ivars bvars model =
  Dy.iter (fun ((id, args), ann) ->
    let check_fun =
      try H.find checkers id
      with Not_found -> raise (No_checker id) in
    let vals = Array.map (eval_expr model ivars bvars) args in
    if not (check_fun vals) then
      begin
        (if !Opts.verbosity > 1 then
          (Util.print_array print_sol Format.err_formatter vals ;
          Format.fprintf Format.err_formatter "@.")) ;
        raise (Not_satisfied id)
      end
    else
      ()) prob.Pr.constraints

let array_int_element args =
  let elts = Pr.get_array Pr.get_int args.(1) in
  let x = Pr.get_int args.(0) in
  let z = Pr.get_int args.(2) in
  1 <= x && x <= Array.length elts &&
  z = elts.(x-1)

let array_bool_element args =
  let elts = Pr.get_array Pr.get_bool args.(1) in
  let x = Pr.get_int args.(0) in
  let z = Pr.get_bool args.(2) in
  1 <= x && x <= Array.length elts &&
  z = elts.(x-1)

let maximum args =
  let xs = Pr.get_array Pr.get_int args.(1) in
  let z = Pr.get_int args.(0) in 
  z = Array.fold_left max xs.(0) xs

let minimum args =
  let xs = Pr.get_array Pr.get_int args.(1) in
  let z = Pr.get_int args.(0) in 
  z = Array.fold_left min xs.(0) xs

let int_linear_rel rel args =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array Pr.get_int args.(1) in
  let k = Pr.get_int args.(2) in
  let vs = Array.init (Array.length xs) (fun i -> cs.(i) * xs.(i)) in
  rel (Array.fold_left (+) 0 vs) k

let bool_linear_rel rel args =
  let cs = Pr.get_array Pr.get_int args.(0) in
  let xs = Pr.get_array Pr.get_bool args.(1) in
  let k = Pr.get_int args.(2) in
  let vs = Array.init (Array.length xs)
    (fun i -> if xs.(i) then cs.(i) else 0) in
  rel (Array.fold_left (+) 0 vs) k

let int_rel rel args =
  let x = Pr.get_int args.(0) in
  let y = Pr.get_int args.(1) in
  rel x y

let int_fun2 f rel args =
  let x = Pr.get_int args.(0) in
  let y = Pr.get_int args.(1) in
  let z = Pr.get_int args.(2) in
  rel (f x y) z

let int_div args =
  let x = Pr.get_int args.(0) in
  let y = Pr.get_int args.(1) in
  let z = Pr.get_int args.(2) in
  y <> 0 && z = x / y

let reif c args =
  (Pr.get_bool (Util.array_last args)) = c args

let imp c args =
  (not (Pr.get_bool (Util.array_last args))) || c args

let bool2int args =
  let b = Pr.get_bool args.(0) in
  let x = Pr.get_int args.(1) in
  x = if b then 1 else 0

let cl_id = ref 0
let bool_clause args =
  incr cl_id ;
  let pos = Pr.get_array Pr.get_bool args.(0) in
  let neg = Pr.get_array Pr.get_bool args.(1) in
  Array.fold_left (||) false
    (Array.append pos (Array.map (fun x -> not x) neg))

let array_bool_and args =
  let xs = Pr.get_array Pr.get_bool args.(0) in
  let z = Pr.get_bool args.(1) in
  z = (Array.fold_left (&&) true xs)

let array_bool_or args =
  let xs = Pr.get_array Pr.get_bool args.(0) in
  let z = Pr.get_bool args.(1) in
  z = (Array.fold_left (||) false xs)

let bool_rel rel args =
  rel (Pr.get_bool args.(0)) (Pr.get_bool args.(1))

let all_different args =
  let xs = Pr.get_array Pr.get_int args.(0) in
  Array.sort compare xs ;
  let sz = Array.length xs in
  let rec aux k =
    if k >= sz then
      true
    else
      xs.(k-1) <> xs.(k) && aux (k+1)
  in
  aux 1

 let all_different_except_0 args =
  let xs = Pr.get_array Pr.get_int args.(0) in
  Array.sort compare xs ;
  let sz = Array.length xs in
  let rec aux k =
    if k >= sz then
      true
    else
      (xs.(k) = 0 || xs.(k-1) <> xs.(k)) && aux (k+1)
  in
  aux 1
 
let table args =
  let xs = Pr.get_array Pr.get_int args.(0) in
  let arity = Array.length xs in
  let ts_flat = Pr.get_array Pr.get_int args.(1) in
  let sz = Array.length ts_flat / arity in
  let rec aux k =
    if k >= sz then
      false
    else
      if xs = Array.init arity (fun i -> ts_flat.(k * arity + i)) then
        true
      else
        aux (k+1)
  in
  aux 0

let cumulative args =
  let s = Pr.get_array Pr.get_int args.(0) in
  let d = Pr.get_array Pr.get_int args.(1) in
  let r = Pr.get_array Pr.get_int args.(2) in
  let b = Pr.get_int args.(3) in  
  (* Only need to check the start positions. *)
  Array.for_all (fun t ->
    (* The sum at time t must be no greater than b. *) 
    let req = ref 0 in
    Array.iteri (fun i r ->
      if s.(i) <= t && t < s.(i) + d.(i) then
        req := !req + r
    ) r ;
    !req <= b
  ) s

(* Initialize the checkers *)
let check_funs =
(*
    ["bool_clause", bool_clause ;
     "int_max", int_max ;
     (* "int_min", int_min ; *)
     "int_times", int_mul ;
     "int_lin_le", int_lin_le ;
     "int_lin_eq", int_lin_eq ;
     "int_lin_ne", int_lin_ne ;
     (* "int_lin_ne", ignore_constraint ; *)
     "int_eq", int_eq ;
     (* "int_ne", int_ne ; *)
     "int_eq_reif", int_eq_reif ;
     "int_ne_reif", int_ne_reif ;
     "bool2int", bool2int ;
     "array_bool_and", array_bool_and ;
     "array_bool_or", array_bool_or ;
     (* "bool_sum_le", bool_sum_le ; *) *)
     [ "bool2int", bool2int ;
       "bool_clause", bool_clause ;
       "int_abs", int_rel (fun x z -> z = abs x) ;
       "int_max", int_fun2 max (=) ;
       "int_min", int_fun2 min (=) ;
       "int_times", int_fun2 ( * ) (=) ;
       "int_div", int_div ;
       "int_plus", int_fun2 (+) (=) ;
       "array_int_maximum", maximum ;
       "array_int_minimum", minimum ;
       "int_eq", int_rel (=) ;
       "int_ne", int_rel (<>) ;
       "int_ne_reif", reif (int_rel (<>)) ;
       "int_ne_imp", imp (int_rel (<>)) ;
       "int_eq_reif", reif (int_rel (=)) ;
       "int_eq_imp", imp (int_rel (=)) ;
       "int_le", int_rel (<=) ;
       "int_le_reif", reif (int_rel (<=)) ;
       "int_le_imp", imp (int_rel (<=)) ;
       "int_lt", int_rel (<) ;
       "int_lt_reif", reif (int_rel (<)) ;
       "int_lin_le_reif", reif (int_linear_rel (<=)) ;
       "int_lin_le", int_linear_rel (<=) ;
       "int_lin_le_reif", reif (int_linear_rel (<=)) ;
       "int_lin_le_imp", imp (int_linear_rel (<=)) ;
       "int_lin_ne", int_linear_rel (<>);
       "int_lin_ne_reif", reif (int_linear_rel (<>));
       "int_lin_eq", int_linear_rel (=) ;
       "int_lin_eq_reif", reif (int_linear_rel (=)) ;
       "bool_eq", bool_rel (=) ;
       "bool_eq_reif", reif (bool_rel (=)) ;
       "bool_lin_le", bool_linear_rel (<=) ;
       "array_int_element", array_int_element ;
       "array_var_int_element", array_int_element ;
       "array_bool_element", array_bool_element ;
       "array_var_bool_element", array_bool_element ;
       "array_bool_and", array_bool_and ; 
       "array_bool_or", array_bool_or ; 
       "all_different_int", all_different ;
       "fzn_all_different_int", all_different ;
       "fzn_all_different_except_0", all_different_except_0 ;
       "fzn_cumulative", cumulative ;
       "fzn_cumulative_var", cumulative ;
       "fzn_table_int", table ;
     ]
let init () =
  List.iter (fun (id, checker) -> H.add checkers id checker) check_funs


let _ = init ()
