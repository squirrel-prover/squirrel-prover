open Utils

(*------------------------------------------------------------------*)
type ident = private {
  name : string;
  tag  : int;
}

type idents = ident list

type t = ident

(*------------------------------------------------------------------*)
val create : string -> ident

val name : ident -> string
val tag  : ident -> int

val fresh : ident -> ident

val equal : ident -> ident -> bool
val compare : ident -> ident -> int
val hash : ident -> int

(** Full ident, with the tag. *)
val to_string : ident -> string

(*------------------------------------------------------------------*)
val pp     : Format.formatter -> ident -> unit
val pp_full: Format.formatter -> ident -> unit

(*------------------------------------------------------------------*)
module Mid : Map.S with type key = ident
module Sid : Set.S with type elt = ident
