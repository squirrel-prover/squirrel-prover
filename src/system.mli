(** The user specifies one or more multi-systems, identified using names.
    An n-system (multi-system of arity n) is a set of n-actions,
    featuring n-ary diff operators, usually obtained from an n-process.

    In this module, system means multi-system. *)

(** A system is indirectly represented by a system symbol. *)
type t = Symbols.system Symbols.t

(** [of_lsymb s tbl] convert [s] to a symbol,
    if it corresponds to a registered system in [tbl]. *)
val of_lsymb : Symbols.lsymb -> Symbols.table -> t

(** Print given system as declared in symbols table. *)
val pp_system : Symbols.table -> Format.formatter -> t -> unit

(** Print all systems declared in symbols table. *)
val pp_systems : Format.formatter -> Symbols.table -> unit

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type system_error = 
  | Shape_error (** Inconsistency between shapes and indices. *)

val pp_system_error : Format.formatter -> system_error -> unit

exception System_error of system_error

(*------------------------------------------------------------------*)
(** {2 Access functions} *)

(** Get a (refreshed) descr.
    @raise Not_found if no action corresponds to the wanted shape. *)
val descr_of_shape :
  Symbols.table -> Symbols.system Symbols.t -> Action.shape -> 
  Action.descr

module Msh : Map.S with type key = Action.shape

(** Return (refreshed) action descriptions of a given system. *)
val descrs : 
  Symbols.table ->
  Symbols.system Symbols.t ->
  Action.descr Msh.t

(** Return all the action symbols of a system. *)
val symbs :
  Symbols.table ->
  Symbols.system Symbols.t ->
  Symbols.action Symbols.t Msh.t

(*------------------------------------------------------------------*)
(** {2 Creating new systems and actions} *)

type Symbols.data +=
  System_data of Action.descr Msh.t * Symbols.action Symbols.t Msh.t
  (** Data that must be associated to each system in the symbols
      table, to be used when declaring directly using [Symbols]. *)

(** Declare a new system, without any associated actions. *)
val declare_empty : Symbols.table -> Symbols.lsymb -> Symbols.table * t

(** Register an action symbol in a system,
  * associating it with an action description.
  * The set of registered actions for this system name will define
  * the protocol under study.
  * Returns the updated table and the actual action symbol and description
  * used (currently the proposed symbol may not be used for technical
  * reasons that will eventually disappear TODO). *)
val register_action :
  Symbols.table -> t ->
  Symbols.action Symbols.t -> Vars.var list ->
  Action.action -> Action.descr -> 
  Symbols.table * Symbols.action Symbols.t * Action.descr
