open Utils

(*------------------------------------------------------------------*)
(** projection used in diff operators. *)
type t

module M : Map.S with type key = t
module S : Set.S with type elt = t

val pp      : t      formatter
val pp_list : t list formatter
  
(** We use strings to identify components of diff operators. *)
val from_string : string -> t
val to_string   : t      -> string

val left  : t
val right : t
