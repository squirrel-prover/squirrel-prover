(** Profiling *)

val record : string -> unit
val is_recorded : string -> bool
val call : string -> float -> unit
val reset_all : unit -> unit

val print : Format.formatter -> unit -> unit

val mk_unary   : string -> ('a -> 'b) -> 'a -> 'b
val mk_binary  : string -> ('a -> 'b -> 'c) -> ('a -> 'b -> 'c)
val mk_ternary : string -> ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
