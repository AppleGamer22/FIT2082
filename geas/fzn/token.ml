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

let kwd_str = function
  | Lpar -> "("
  | Rpar -> ")"
  | Lbrak -> "["
  | Rbrak -> "]"
  | Lbrace -> "{"
  | Rbrace -> "}"
  | Comma -> ","
  | Ddot -> ".."
  | Semi -> ";"
  | Colon -> ":"
  | Dcolon -> "::"
  | BoolT -> "bool"
  | IntT -> "int"
  | FloatT -> "float"
  | ArrayK -> "array"
  | Of -> "of"
  | Any -> "any"
  | Var -> "var"
  | Par -> "par"
  | Annot -> "annotation"
  | Eq -> "="
  | Constraint -> "constraint"
  | Pred -> "predicate"
  | Solve -> "solve"
  | Satisfy -> "satisfy"
  | Maximize -> "maximize"
  | Minimize -> "minimize"

let tok_str = function
| Id s -> s
| Str s -> "\"" ^ s ^ "\""
| Int k -> string_of_int k
| Float k -> string_of_float k
| Bool b -> if b then "true" else "false"
| Kwd k -> kwd_str k
