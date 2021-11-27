(* Defining tokesn for the FlatZinc lexer *)
(* Keywords *)
type kwd =
  | Lpar | Rpar | Lbrak | Rbrak | Lbrace | Rbrace
  | Comma | Ddot | Semi | Colon | Dcolon
  | BoolT | IntT | FloatT | ArrayK | Of | Any
  | Var | Par
  | Annot
  | Eq
  | Constraint | Pred | Solve
  | Satisfy | Maximize | Minimize

type token = 
  (* Usual data *)
  Id of string
| Str of string
| Int of int
| Float of float
| Bool of bool
| Kwd of kwd
  
type t = token

val tok_str : t -> string
