(* Recursive-descent parser for FlatZinc. *)
exception Tok_error of Token.t

val lexer : in_channel -> Token.t Stream.t

(*
val read_item :
  (Lexing.lexbuf -> Fzn_token.t) -> Fzn_model.t ->
  Lexing.lexbuf -> unit
  *)

val read_item : Problem.t -> Token.t Stream.t -> unit

val read_problem : Token.t Stream.t -> Problem.t
