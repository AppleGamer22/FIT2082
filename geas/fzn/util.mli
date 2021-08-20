(** Various helper functions *)
exception Not_yet

val div_floor : int -> int -> int
val div_ceil : int -> int -> int
val gcd_list : int list -> int
val gcd : int -> int -> int

module HashSet :
sig
  type 'a t

  val create : int -> 'a t

  val add : 'a t -> 'a -> unit
  val remove : 'a t -> 'a -> unit
  val elem : 'a t -> 'a -> bool
  val clear : 'a t -> unit

  val elements : 'a t -> 'a list
end

module WorkList :
sig
  type 'a t

  val create : unit -> 'a t

  val push : 'a t -> 'a -> unit
  val pop : 'a t -> 'a
  val clear : 'a t -> unit
  val is_empty : 'a t -> bool
end

val hashtbl_map : ('k -> 'a -> 'b) -> ('k, 'a) Hashtbl.t -> ('k, 'b) Hashtbl.t
val print_array : (Format.formatter -> 'a -> unit) ->
  ?pre:((unit, Format.formatter, unit) format) ->
  ?sep:((unit, Format.formatter, unit) format) ->
  ?post:((unit, Format.formatter, unit) format) ->
  Format.formatter -> 'a array -> unit

val print_list : (Format.formatter -> 'a -> unit) ->
  ?pre:((unit, Format.formatter, unit) format) ->
  ?sep:((unit, Format.formatter, unit) format) ->
  ?post:((unit, Format.formatter, unit) format) ->
  Format.formatter -> 'a list -> unit

val array_last : 'a array -> 'a
val array_drop : 'a array -> 'a array

val array_everyi : (int -> 'a -> bool) -> 'a array -> bool
val array_foldi : (int -> 'r -> 'a -> 'r) -> 'r -> 'a array -> 'r
val array_fold2 : ('r -> 'a -> 'b -> 'r) -> 'r -> 'a array -> 'b array -> 'r

val array_combine : 'a array -> 'b array -> ('a * 'b) array

val array_fold1 : ('a -> 'a -> 'a) -> 'a array -> 'a
