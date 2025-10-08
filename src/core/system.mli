(** Syntax for systems. 
    More functions are defined in the [System] module. *)

(*------------------------------------------------------------------*)
open Utils

(*------------------------------------------------------------------*)
include module type of SystemSyntax

(*------------------------------------------------------------------*)
(** The list of projections of a system. *)
val projections : Symbols.table -> t -> Projection.t list

(** Check whether a system supports a given projection. *)
val valid_projection : Symbols.table -> t -> Projection.t -> bool

(** Indicates whether a system supports a given projection
    and this projection is well-typed w.r.t. the secrecy type system. *)
val well_typed_projection : Symbols.table -> t -> Projection.t -> bool

(*------------------------------------------------------------------*)
(** Check that two systems are strongly compatible.
    This implies the theoretical notion of compatibility,
    and relies on [Action.strongly_compatible_descr] to ensure
    that descriptions can be merged later on. *)
val compatible : Symbols.table -> t -> t -> bool

(*------------------------------------------------------------------*)
(** Convert a symbol to a system. *)
val convert : Symbols.table -> Symbols.p_path -> t
(** The execution model of a system. *)
val exec_model : Symbols.table -> t -> Action.exec_model

(*------------------------------------------------------------------*)
(** Print given system as declared in symbols table. *)
val pp_system : Symbols.table -> t formatter

(** Print all systems declared in symbols table. *)
val pp_systems : Symbols.table formatter


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

(** Declare a new n-system with associated execution model, 
    projections, and without any associated actions.
    Fails if [name] is already in use. *)
val declare_empty :
  Symbols.table -> Action.exec_model -> Symbols.lsymb -> Projection.t list-> 
  Symbols.table * t

(** Register an action symbol in a system,
    associating it with an action description.
    The set of registered actions for this system name will define
    the protocol under study.
    Returns the updated table and the actual action symbol and description
    used (currently the proposed symbol may not be used for technical
    reasons that will eventually disappear TODO). *)
val register_action :
  Symbols.table -> t -> Action.descr ->
  Symbols.table * Symbols.action * Action.descr

(** Modify the list of well typed projection stored in the table for a
  * given system.
  * Returns the updated table. *)
val add_well_typed :
  Symbols.table -> t -> Projection.t list -> Symbols.table

(** Removes the list of well typed projection stored in the table for any
  * system.
  * Returns the updated table. *)
val remove_all_well_typed :
  Symbols.table -> Symbols.table

(*------------------------------------------------------------------*)
(** {2 Single systems} *)

module Single : sig

  include module type of SystemSyntax.Single

  (** Safe single system constructor *)
  val make : Symbols.table -> Symbols.system -> Projection.t -> t

  val descr_of_shape : Symbols.table -> t -> Action.shape -> Action.descr
end
