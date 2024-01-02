(** Profiling *)

val is_recorded : string -> bool
val reset_all : unit -> unit

val print : Format.formatter -> unit -> unit

val mk_unary   : string -> ('a -> 'b) -> 'a -> 'b
val mk_binary  : string -> ('a -> 'b -> 'c) -> ('a -> 'b -> 'c)
val mk_ternary : string -> ('a -> 'b -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd

(** General interface *)

(** A ['a profiler] is used to call [unit -> 'a] functions,
    and record the total number of such calls and their duration. *)
type 'a profiler = (unit -> 'a) -> 'a

(** Return a new profiler which records calls and duration under
    the given name. *)
val mk : string -> 'a profiler