(* Lexer for FlatZinc. *)
{
open Token

let keywords = Hashtbl.create 17

let get_ident str =
  try
    Hashtbl.find keywords str
  with Not_found -> Id str
}

let digit = ['0' - '9']
let lower = ['a' - 'z']
let upper = ['A' - 'Z']
let alpha = lower | upper
let alnum = alpha | digit
let alext = alnum | ':' | '_' | '''

let sym = lower alext*
let ident = (alpha | '_') (alnum | '_')*
let comment = '%' [^ '\n']* '\n'
let strchar = [^ '"' '\\'] | ('\\' _)

rule token = parse
    [' ' '\t'] { token lexbuf }
  | comment { token lexbuf }
  | ['\n'] { token lexbuf }
  | (('-'?)digit)+ as lxm { Int (int_of_string lxm) }
  | '-'? digit+ '.' digit+ (['e' 'E'] digit+)? as lxm
      { Float (float_of_string lxm) }
  | ident as lxm  { get_ident lxm }
  | '"' (strchar* as s) '"' { Str s }
  | "=" { Kwd Eq }
  (*
  | "<=" { Kwd Le }
  | "<" { Kwd Lt }
  | ">=" { Kwd Gt }
  | ">" { TOK_GT }
  | "!=" { TOK_NE }
  | "=" { TOK_EQ }
  *)
  | ".." { Kwd Ddot }
  (*
  | '.' { TOK_STOP }
  *)
  | '(' { Kwd Lpar }
  | ')' { Kwd Rpar }
  | '[' { Kwd Lbrak }
  | ']' { Kwd Rbrak }
  | '{' { Kwd Lbrace }
  | '}' { Kwd Rbrace }
  | ':' { Kwd Colon }
  | "::" { Kwd Dcolon }
  | ';' { Kwd Semi }
  | ',' { Kwd Comma }
  (*
  | '+' { Kwd Plus }
  | '-' { Kwd Minus }
  | '*' { TOK_MUL }
  | '/' { TOK_DIV }
  | '%' { TOK_PERC }
  | '|' { TOK_PIPE }
  | eof { TOK_EOF }
  *)

{
(* Set up keyword table *)
let kw_toks =
  [ "true", Bool true ;
    "false", Bool false ;
    "annotation", Kwd Annot ;
    "any", Kwd Any ;
    "bool", Kwd BoolT ;
    "int", Kwd IntT ;
    "float", Kwd FloatT ;
    "array", Kwd ArrayK ;
    "of", Kwd Of ;
    "par", Kwd Par ;
    "var", Kwd Var ;
    "constraint", Kwd Constraint ;
    "predicate", Kwd Pred ;
    "solve", Kwd Solve ;
    "satisfy", Kwd Satisfy ;
    "minimize", Kwd Minimize ;
    "maximize", Kwd Maximize ]
   
let init_keywords tbl =
  List.iter (fun (k, t) -> Hashtbl.add tbl k t) kw_toks

let _ = init_keywords keywords

}
