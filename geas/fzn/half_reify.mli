(** Replace full- with half-reification where possible *)

(** Initialize rewriting rules *)
val initialize : unit -> unit

(** Rewrite a problem *)
val half_reify : ?ctxs:Polarity.t -> Simplify.t -> Simplify.t
