(** The user specifies one or more (bi)systems, identified using names.
  * Each (bi)system is a set of (bi)actions, obtained from a (bi)process. *)

type system_name = Symbols.system Symbols.t

val pp_system : Symbols.table -> Format.formatter -> system_name -> unit

val pp_systems : Format.formatter -> Symbols.table -> unit

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type system_error = 
  | SE_ShapeError

val pp_system_error : Format.formatter -> system_error -> unit

exception SystemError of system_error


(*------------------------------------------------------------------*)
(** {2 Access functions} *)

type lsymb = Symbols.lsymb

val of_lsymb : lsymb -> Symbols.table -> system_name

(** Declare a new system, without any associated actions. *)
val declare_empty : Symbols.table -> lsymb -> Symbols.table * system_name

(** Get a (refreshed) descr.
    @Raise Not_found if no action corresponds to the wanted shape. *)
val descr_of_shape :
  Symbols.table -> Symbols.system Symbols.t -> Action.shape -> 
  Action.descr

module Msh : Map.S with type key = Action.shape

type Symbols.data +=
  System_data of Action.descr Msh.t * Symbols.action Symbols.t Msh.t

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
(** {2 Registration of actions} *)

(** Register an action symbol in a system,
  * associating it with an action description.
  * The set of registered actions for this system name will define
  * the protocol under study.
  * Returns the updated table and the actual action symbol and description
  * used * (currently the proposed symbol may not be used for technical
  * reasons that will eventually disappear TODO). *)
val register_action :
  Symbols.table -> system_name ->
  Symbols.action Symbols.t -> Vars.index list ->
  Action.action -> Action.descr -> 
  Symbols.table * Symbols.action Symbols.t * Action.descr
