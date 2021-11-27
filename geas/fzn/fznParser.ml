(* Recursive-descent parser for FlatZinc. *)
open Token
module S = Stream
module Lex = FznLexer
module M = Problem

exception Tok_error of Token.t

let debug_printf (fstr : ('a, Format.formatter, unit) format) =
  if !Opts.verbosity > 1 then
    Format.fprintf Format.err_formatter fstr

(* Convert the ocamllex lexer into a Stream.t *)
let lexer channel =
  let lexbuf = Lexing.from_channel channel in
  Stream.from (fun i ->
    try
      Some (Lex.token lexbuf)
    with _ -> None)

let chomp lex expected =
  let curr = S.next lex in
  if curr <> expected then
    raise (S.Error
      (Format.sprintf "Expected %s, instead got %s"
        (tok_str expected) (tok_str curr)))
  else
    ()

let parse_int toks =
  match S.next toks with
  | Int k -> k
  | tok -> raise (S.Error (Format.sprintf
                          "Expected int, got %s."
                          (tok_str tok)))

let parse_float toks =
  match S.next toks with
  | Int k -> float_of_int k
  | Float k -> k
  | tok -> raise (S.Error (Format.sprintf
                          "Expected float, got %s."
                          (tok_str tok)))

let parse_ident toks =
  match S.next toks with
  | Id id -> id
  | tok -> raise (S.Error (Format.sprintf
                          "Expected ident, got %s."
                          (tok_str tok)))

let parse_tail item toks =
  let rec aux acc =
    match S.peek toks with
    | Some (Kwd Comma) -> (S.junk toks ; aux (item toks :: acc))
    | _ -> List.rev acc
  in
  aux []

let parse_seq item pre post toks =
  chomp toks pre ;
  if S.peek toks = Some post then
    (S.junk toks ; [])
  else
    let k = item toks in
    let tl = parse_tail item toks in
    (chomp toks post; k :: tl)

let parse_array item toks =
  Array.of_list (parse_seq item (Kwd Lbrak) (Kwd Rbrak) toks)

let parse_range toks =
  let lb = parse_int toks in
  chomp toks (Kwd Ddot) ;
  let ub = parse_int toks in
  Dom.range lb ub

let parse_set toks = parse_seq parse_int (Kwd Lbrace) (Kwd Rbrace) toks
  
let must_peek toks =
  match S.peek toks with
  | Some t -> t
  | None -> failwith "must_peek on empty stream."

let junk_upto toks tok =
  while S.peek toks <> Some tok
  do
    S.junk toks
  done ;
  S.junk toks

let parse_range toks =
  let l = parse_int toks in
  chomp toks (Kwd Ddot) ;
  Dom.range l (parse_int toks)

let parse_int_or_range toks =  
  let x = parse_int toks in
  if S.peek toks = Some (Kwd Ddot) then
    (S.junk toks ; M.Set (Dom.range x (parse_int toks)))
  else
    M.Ilit x

let rec parse_expr model toks =
  match must_peek toks with
  | Int k -> (* (S.junk toks ; M.Ilit k) *)
      parse_int_or_range toks
  | Bool b -> (S.junk toks ; M.Blit b)
  | Id id -> (S.junk toks; M.resolve model id)
    (* parse_id_or_call model toks *)
    (* Either an identifier, or the start of a call. *)
  | (Kwd Lbrak) -> M.Arr (parse_array (parse_expr model) toks)
  | (Kwd Lbrace) -> M.Set (Dom.set (parse_set toks))
  | tok -> raise (Tok_error tok)
(*
and parse_id_or_call model toks =
  let id = parse_ident toks in
  if S.peek toks = Some (Kwd Lpar) then
     M.Call (id, parse_seq (parse_expr model) (Kwd Lpar) (Kwd Rpar) toks)
   else
     M.resolve model id
*)

(* FIXME: what do we do about name resolution in annotations?
 * Consider :: int_search([x, y], input_order, indomain_max, complete);
 * [x, y] should be resolved to the corresponding vars, but
 * the rest left uninterpreted. *)


let parse_ann_int_or_range toks =
  let l = parse_int toks in
  if S.peek toks = Some (Kwd Ddot) then
    (S.junk toks; M.Ann_set (Dom.range l (parse_int toks)))
  else
    M.Ann_int l

let rec parse_ann toks =
  match must_peek toks with
  | Int k -> parse_ann_int_or_range toks
    (* parse_int_or_range toks *)
  | Bool b -> (S.junk toks ; M.Ann_bool b)
  | Str s -> (S.junk toks ; M.Ann_str s)
  | Id id -> parse_ann_id_or_call toks
  | (Kwd Lbrak) -> M.Ann_arr (parse_array parse_ann toks)
  | (Kwd Lbrace) -> M.Ann_set (Dom.set (parse_set toks))
  | tok -> raise (Tok_error tok)
and parse_ann_id_or_call toks =
  let id = parse_ident toks in
  if S.peek toks = Some (Kwd Lpar) then
    let args = parse_seq parse_ann (Kwd Lpar) (Kwd Rpar) toks in
    M.Ann_call (id, Array.of_list args)
  else
    M.Ann_id id

let parse_anns toks =
  let rec aux acc =
    if S.peek toks = Some (Kwd Dcolon) then
      (chomp toks (Kwd Dcolon) ; aux (parse_ann toks :: acc))
    else
      List.rev acc
  in aux []

(* Ignore predicate declarations *)
let parse_pred model toks =
  (* debug_printf "Pred@." ; *)
  junk_upto toks (Kwd Semi)

let read_constraint model toks =
  (* debug_printf "Cstr@." ; *)
  chomp toks (Kwd Constraint) ;
  let id = parse_ident toks in
  let args =
    Array.of_list
      (parse_seq (parse_expr model) (Kwd Lpar) (Kwd Rpar) toks) in 
  let anns = parse_anns toks in
  M.post model id args anns ;
  chomp toks (Kwd Semi)

(* Format of declarations:
 * solve [anns] (satisfy | maximize <id> | minimize <id>) *)
let parse_obj model toks =
  match M.resolve model (parse_ident toks) with
  | M.Ivar v -> v
  | M.Arr a ->
    begin
      chomp toks (Kwd Lbrak) ;
      let v =
        match a.(parse_int toks) with
        | M.Ivar v -> v
        | _ -> failwith "Subscripted objective should resolve to var int."
      in
      chomp toks (Kwd Rbrak) ;
      v
    end
  | _ -> failwith "Objective must resolve to var int."

let read_solve model toks =
  (* debug_printf "Solve@." ; *)
  chomp toks (Kwd Solve) ;
  let anns = parse_anns toks in
  let goal =
    match S.next toks with
    | Kwd Minimize -> M.Minimize (parse_obj model toks)
    | Kwd Maximize -> M.Maximize (parse_obj model toks)
    | Kwd Satisfy -> M.Satisfy
    | tok ->
      failwith (Format.sprintf
                 "Expected (satisfy | minimize | maximize), got %s."
                 (tok_str tok)) in
  model.M.objective <- (goal, anns) ;
  chomp toks (Kwd Semi)

(* Format of declarations:
 * typeinst: id [anns] [= expr]; *)

(* This is _slightly_ dodgy.
 * Make more robust eventually *)
let read_bool toks =
  match S.next toks with
  | Bool b -> b
  | _ -> failwith "Expected bool literal"

let read_int toks =
  match S.next toks with
  | Int k -> k
  | _ -> failwith "Expected int linteral"

let read_bvar_decl model toks =
  chomp toks (Kwd BoolT) ;
  chomp toks (Kwd Colon) ;
  let id = parse_ident toks in
  let anns = parse_anns toks in
  if S.peek toks = Some (Kwd Eq) then
    begin
      S.junk toks ;
      match S.next toks with
      | Bool b -> M.bind model id (M.Blit b) anns
      | Id id' -> M.bind model id (M.resolve model id')  anns
      | _ -> failwith "Unexpected token in binding."
    end
  else
    M.bind model id (M.Bvar (M.new_bvar model id anns)) [] ;
  chomp toks (Kwd Semi)

let default_imax = 1 lsl 26
let warn_unbounded =
  let warned = ref false in
  (fun () ->
    if not !warned then
      Format.fprintf Format.err_formatter
        "%%%% WARNING: unbounded integer variable, using default bounds [%d, %d].@."
        (- default_imax) (default_imax) ;
      warned := true)

let read_ivar_decl model toks =
  let dom =
    match must_peek toks with
    | Int _ -> parse_range toks
    | Kwd Lbrace -> Dom.Set (parse_set toks)
    | Kwd IntT ->
      S.junk toks;
      warn_unbounded () ;
      Dom.Range (- default_imax, default_imax)
    | _ -> failwith "Expected integer domain"
  in
  chomp toks (Kwd Colon) ; 
  let id = parse_ident toks in
  let anns = parse_anns toks in
  if S.peek toks = Some (Kwd Eq) then
    begin
      S.junk toks ;
      match S.next toks with
      | Int k -> M.bind model id (M.Ilit k) anns
      | Id id' -> M.bind model id (M.resolve model id') anns
      | _ -> failwith "Unexpected token in binding."
    end
  else
    M.bind model id (M.Ivar (M.new_ivar model id dom anns)) [] ;
  chomp toks (Kwd Semi)

let read_var_decl model toks =
  chomp toks (Kwd Var) ;
  (* One of: bool, int, a range or a set *)
  match must_peek toks with
  | Kwd BoolT -> read_bvar_decl model toks
  | _ -> read_ivar_decl model toks
  (*
  let declare = 
    match must_peek toks with
    | Kwd BoolT -> (S.junk toks; fun id anns -> M.Bvar (M.new_bvar model id anns))
    (* | Kwd IntT -> (S.junk toks ; M.Ivar (M.new_ival model Dom.free)) *)
    | Kwd Lbrace ->
        (* An array literal *)
        let vals = parse_set toks in
        (fun id anns -> M.Ivar (M.new_ivar model id (Dom.Set vals) anns))
    | Int _ ->
        let dom = parse_range toks in
        (fun id anns -> M.Ivar (M.new_ivar model id dom anns))
    | _ -> failwith "Expected var domain"
  in
  chomp toks (Kwd Colon) ;
  let id = parse_ident toks in
  let anns = parse_anns toks in
  chomp toks (Kwd Semi) ;
  M.bind model id (declare id anns)
*)

let read_decl model toks =
  (* debug_printf "Decl@." ; *)
  match must_peek toks with
  | Kwd Var -> read_var_decl model toks
  | _ ->
    (* Only other possibility is array *)
    begin
      junk_upto toks (Kwd Colon) ;
      let id = parse_ident toks in
      let anns = parse_anns toks in
      chomp toks (Kwd Eq) ;
      let expr = parse_expr model toks in
      chomp toks (Kwd Semi) ;
      M.bind model id expr anns
    end

let read_item model toks =
  match S.peek toks with
  | Some (Kwd Pred) -> parse_pred model toks
  | Some (Kwd Constraint) -> read_constraint model toks
  | Some (Kwd Solve) -> read_solve model toks
  | Some _ -> read_decl model toks
  | None -> raise (S.Error "Unexpected end of tokens.")

let read_problem toks =
  let model = M.create () in
  while S.peek toks <> None do
    read_item model toks
  done ;
  model
