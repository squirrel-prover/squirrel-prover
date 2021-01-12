(** The user specifies one or more (bi)systems, identified using names.
  * Each (bi)system is a set of (bi)actions, obtained from a (bi)process. *)

type system_name = Symbols.system Symbols.t

(** Declare a new system, without any associated actions. *)
val declare_empty : Symbols.table -> string -> Symbols.table * system_name

(** Convert action to the corresponding [Action] timestamp term in
    a bi-system. *)
val action_to_term : 
  Symbols.table -> system_name -> Action.action -> Term.timestamp

(** Specify if a given system name is not already in use. *)
val is_fresh : string -> Symbols.table -> bool

(** @Raise Not_found if no action corresponds to the wanted shape. *)
val descr_of_shape :
  Symbols.table -> Symbols.system Symbols.t -> Action.shape -> 
  Action.descr

(** Get dummy action of some length. Guarantees that a symbol exists 
    for it. *)
val dummy_action : int -> Action.action

module Msh : Map.S with type key = Action.shape

type Symbols.data += System_data of Action.descr Msh.t

(** Return all the action descriptions of a given system. *)
val descrs : 
  Symbols.table ->
  Symbols.system Symbols.t ->
  Action.descr Msh.t

(*------------------------------------------------------------------*)
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
  Symbols.table -> system_name ->
  Symbols.action Symbols.t -> Vars.index list ->
  Action.action -> Action.descr -> 
  Symbols.table * Symbols.action Symbols.t
