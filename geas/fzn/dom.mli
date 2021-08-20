(* Representation of domains for preprocessing *)
type t =
  | Range of int * int
  | Set of int list

val range : int -> int -> t
val set : int list -> t

val union : t -> t -> t
val intersect : t -> t -> t option

val bounds : t -> (int * int)
val holes : t -> (int * int) list

val lb : t -> int
val ub : t -> int
val size : t -> int

val neg : t -> t
val add : t -> int -> t
