(** The user specifies one or more (bi)systems, identified using names.
  * Each (bi)system is a set of (bi)actions, obtained from a (bi)process. *)

include module type of Symbols.System

type system_name = Symbols.system Symbols.t

(** Specify if a given system name is not already in use. *)
val is_fresh : Symbols.system Symbols.t -> Symbols.table -> bool

(** @Raise Not_found if no action corresponds to the wanted shape. *)
val descr_of_shape :
  Symbols.table -> Symbols.system Symbols.t -> Action.shape -> 
  Action.descr

module Msh : Map.S with type key = Action.shape

val descrs : 
  Symbols.table ->
  Symbols.system Symbols.t ->
  Action.descr Msh.t

(** {2 Registration of actions} *)

exception SystemError of string

(** Register an action symbol in a system,
  * associating it with an action description.
  * The set of registered actions for this system name will define
  * the protocol under study.
  * Returns the updated table and the actual action symbol used
  * (currently the proposed symbol may not be used for technical
  * reasons that will eventually disappear TODO). *)
val register_action :
  Symbols.table -> Symbols.system Symbols.t ->
  Symbols.action Symbols.t -> Vars.index list ->
  Action.action -> Action.descr -> 
  Symbols.table * Symbols.action Symbols.t
