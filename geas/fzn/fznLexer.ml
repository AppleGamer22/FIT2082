# 2 "fznLexer.mll"
 
open Token

let keywords = Hashtbl.create 17

let get_ident str =
  try
    Hashtbl.find keywords str
  with Not_found -> Id str

# 13 "fznLexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base =
   "\000\000\237\255\238\255\002\000\241\255\242\255\243\255\244\255\
    \245\255\246\255\001\000\248\255\002\000\078\000\156\000\166\000\
    \253\255\001\000\255\255\254\255\176\000\186\000\199\000\211\000\
    \221\000\233\000\249\255\023\000\247\255\239\255";
  Lexing.lex_backtrk =
   "\255\255\255\255\255\255\015\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\005\000\003\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\003\000\004\000\
    \255\255\004\000\255\255\255\255\255\255\255\255";
  Lexing.lex_default =
   "\255\255\000\000\000\000\255\255\000\000\000\000\000\000\000\000\
    \000\000\000\000\255\255\000\000\012\000\255\255\255\255\255\255\
    \000\000\017\000\000\000\000\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\000\000\012\000\000\000\000\000";
  Lexing.lex_trans =
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\018\000\016\000\019\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \018\000\000\000\012\000\000\000\026\000\017\000\000\000\000\000\
    \009\000\008\000\000\000\000\000\001\000\015\000\010\000\028\000\
    \014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
    \014\000\014\000\003\000\002\000\029\000\011\000\000\000\000\000\
    \000\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\007\000\000\000\006\000\027\000\013\000\
    \000\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\005\000\000\000\004\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\000\000\000\000\000\000\000\000\013\000\000\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\021\000\020\000\000\000\014\000\014\000\014\000\014\000\
    \014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
    \014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
    \023\000\023\000\023\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\022\000\022\000\022\000\021\000\000\000\000\000\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\255\255\255\255\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\025\000\025\000\025\000\025\000\255\255\
    \024\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000";
  Lexing.lex_check =
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\017\000\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\000\000\255\255\012\000\000\000\255\255\255\255\
    \000\000\000\000\255\255\255\255\000\000\000\000\000\000\010\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\003\000\000\000\255\255\255\255\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\012\000\000\000\
    \255\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\255\255\000\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\255\255\255\255\255\255\255\255\013\000\255\255\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
    \013\000\014\000\014\000\255\255\014\000\014\000\014\000\014\000\
    \014\000\014\000\014\000\014\000\014\000\014\000\015\000\015\000\
    \015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\021\000\021\000\021\000\021\000\021\000\021\000\
    \021\000\021\000\021\000\021\000\022\000\255\255\255\255\022\000\
    \022\000\022\000\022\000\022\000\022\000\022\000\022\000\022\000\
    \022\000\017\000\012\000\023\000\023\000\023\000\023\000\023\000\
    \023\000\023\000\023\000\023\000\023\000\024\000\024\000\024\000\
    \024\000\024\000\024\000\024\000\024\000\024\000\024\000\027\000\
    \023\000\025\000\025\000\025\000\025\000\025\000\025\000\025\000\
    \025\000\025\000\025\000\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \023\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255";
  Lexing.lex_base_code =
   "";
  Lexing.lex_backtrk_code =
   "";
  Lexing.lex_default_code =
   "";
  Lexing.lex_trans_code =
   "";
  Lexing.lex_check_code =
   "";
  Lexing.lex_code =
   "";
}

let rec token lexbuf =
   __ocaml_lex_token_rec lexbuf 0
and __ocaml_lex_token_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 26 "fznLexer.mll"
               ( token lexbuf )
# 177 "fznLexer.ml"

  | 1 ->
# 27 "fznLexer.mll"
            ( token lexbuf )
# 182 "fznLexer.ml"

  | 2 ->
# 28 "fznLexer.mll"
           ( token lexbuf )
# 187 "fznLexer.ml"

  | 3 ->
let
# 29 "fznLexer.mll"
                      lxm
# 193 "fznLexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 29 "fznLexer.mll"
                          ( Int (int_of_string lxm) )
# 197 "fznLexer.ml"

  | 4 ->
let
# 30 "fznLexer.mll"
                                                  lxm
# 203 "fznLexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 31 "fznLexer.mll"
      ( Float (float_of_string lxm) )
# 207 "fznLexer.ml"

  | 5 ->
let
# 32 "fznLexer.mll"
             lxm
# 213 "fznLexer.ml"
= Lexing.sub_lexeme lexbuf lexbuf.Lexing.lex_start_pos lexbuf.Lexing.lex_curr_pos in
# 32 "fznLexer.mll"
                  ( get_ident lxm )
# 217 "fznLexer.ml"

  | 6 ->
let
# 33 "fznLexer.mll"
                     s
# 223 "fznLexer.ml"
= Lexing.sub_lexeme lexbuf (lexbuf.Lexing.lex_start_pos + 1) (lexbuf.Lexing.lex_curr_pos + -1) in
# 33 "fznLexer.mll"
                            ( Str s )
# 227 "fznLexer.ml"

  | 7 ->
# 34 "fznLexer.mll"
        ( Kwd Eq )
# 232 "fznLexer.ml"

  | 8 ->
# 43 "fznLexer.mll"
         ( Kwd Ddot )
# 237 "fznLexer.ml"

  | 9 ->
# 47 "fznLexer.mll"
        ( Kwd Lpar )
# 242 "fznLexer.ml"

  | 10 ->
# 48 "fznLexer.mll"
        ( Kwd Rpar )
# 247 "fznLexer.ml"

  | 11 ->
# 49 "fznLexer.mll"
        ( Kwd Lbrak )
# 252 "fznLexer.ml"

  | 12 ->
# 50 "fznLexer.mll"
        ( Kwd Rbrak )
# 257 "fznLexer.ml"

  | 13 ->
# 51 "fznLexer.mll"
        ( Kwd Lbrace )
# 262 "fznLexer.ml"

  | 14 ->
# 52 "fznLexer.mll"
        ( Kwd Rbrace )
# 267 "fznLexer.ml"

  | 15 ->
# 53 "fznLexer.mll"
        ( Kwd Colon )
# 272 "fznLexer.ml"

  | 16 ->
# 54 "fznLexer.mll"
         ( Kwd Dcolon )
# 277 "fznLexer.ml"

  | 17 ->
# 55 "fznLexer.mll"
        ( Kwd Semi )
# 282 "fznLexer.ml"

  | 18 ->
# 56 "fznLexer.mll"
        ( Kwd Comma )
# 287 "fznLexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf;
      __ocaml_lex_token_rec lexbuf __ocaml_lex_state

;;

# 67 "fznLexer.mll"
 
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


# 322 "fznLexer.ml"