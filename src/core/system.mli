(** The user specifies one or more multi-systems, identified using names.
    An n-system (multi-system of arity n) is a set of n-actions,
    featuring n-ary diff operators, usually obtained from an n-process.

    In this module, system means multi-system. *)

(** A system is indirectly represented by a system symbol. *)
type t = Symbols.system 

(*------------------------------------------------------------------*)
(** Indicates the list of projections of a system. *)
val projections : Symbols.table -> t -> Term.proj list

(** Indicates whether a system supports a given projection. *)
val valid_projection : Symbols.table -> t -> Term.proj -> bool

(*------------------------------------------------------------------*)
(** Check that two systems are strongly compatible.
    This implies the theoretical notion of compatibility,
    and relies on [Action.strongly_compatible_descr] to ensure
    that descriptions can be merged later on. *)
val compatible : Symbols.table -> t -> t -> bool

(*------------------------------------------------------------------*)
(** [of_lsymb tbl s] convert [s] to a symbol,
    if it corresponds to a registered system in [tbl]. *)
val of_lsymb : Symbols.table -> Symbols.lsymb -> t

(*------------------------------------------------------------------*)
(** Print given system as declared in symbols table. *)
val pp_system : Symbols.table -> Format.formatter -> t -> unit

(** Print all systems declared in symbols table. *)
val pp_systems : Format.formatter -> Symbols.table -> unit

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type error =
  | Shape_error        (** Inconsistency between shapes and indices. *)
  | Invalid_projection

val pp_error : Format.formatter -> error -> unit

exception Error of error

(*------------------------------------------------------------------*)
(** {2 Access functions} *)

(** Get a (refreshed) descr.
    @raise Not_found if no action corresponds to the wanted shape. *)
val descr_of_shape :
  Symbols.table -> Symbols.system -> Action.shape ->
  Action.descr

module Msh : Map.S with type key = Action.shape

(** Return (refreshed) action descriptions of a given system. *)
val descrs :
  Symbols.table ->
  Symbols.system ->
  Action.descr Msh.t

(** Return all the action symbols of a system. *)
val symbs :
  Symbols.table ->
  Symbols.system ->
  Symbols.action Msh.t

(*------------------------------------------------------------------*)
(** {2 Creating new systems and actions} *)

(** Declare a new n-system with associated projections,
    without any associated actions.
    Fails if name is already in use. *)
val declare_empty :
  Symbols.table -> Symbols.lsymb -> Term.proj list-> Symbols.table * t

(** Register an action symbol in a system,
  * associating it with an action description.
  * The set of registered actions for this system name will define
  * the protocol under study.
  * Returns the updated table and the actual action symbol and description
  * used (currently the proposed symbol may not be used for technical
  * reasons that will eventually disappear TODO). *)
val register_action :
  Symbols.table -> t -> Action.descr ->
  Symbols.table * Symbols.action * Action.descr

(*------------------------------------------------------------------*)
(** {2 Single systems} *)

module Single : sig

  type t = private {
    system     : Symbols.system ;
    projection : Term.proj
  }

  (** A single system is obtained by taking a valid projection
      of a multi-system, identified by a system symbol.

      Note that the projection is only validated against the current table,
      and is then not attached to this particular table.
      This shouldn't be too bad because we never override system
      symbols after their complete definition. *)
  val make : Symbols.table -> Symbols.system -> Term.proj -> t

  val pp : Format.formatter -> t -> unit

  val descr_of_shape : Symbols.table -> t -> Action.shape -> Action.descr
end
