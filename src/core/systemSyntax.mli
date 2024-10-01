(** The user specifies one or more multi-systems, identified using names.
    An n-system (multi-system of arity n) is a set of n-actions,
    featuring n-ary diff operators, usually obtained from an n-process.

    In this module, system means multi-system. *)

(*------------------------------------------------------------------*)
open Utils

(*------------------------------------------------------------------*)
(** A system is indirectly represented by a system symbol. *)
type t = Symbols.system

(*------------------------------------------------------------------*)
(** Convert a symbol to a system. *)
val convert : Symbols.table -> Symbols.p_path -> t

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type error =
  | Shape_error        (** Inconsistency between shapes and indices. *)
  | Invalid_projection

val pp_error : error formatter

exception Error of error

val error : error -> 'a

(*------------------------------------------------------------------*)
(** {2 Single systems} *)

module Single : sig

  (** A single system is obtained by taking a valid projection
      of a multi-system, identified by a system symbol. *)
  type t = private {
    system     : Symbols.system ;
    projection : Projection.t
  }

  val make_unsafe : Symbols.system -> Projection.t -> t

  val pp : t formatter

  module Map : Map.S with type key = t
  module Set : Set.S with type elt = t
end
