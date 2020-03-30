(** Actions are the basis of our internal semantics for protocols. *)

(** Actions uniquely describe execution points in a protocol.
  * They consist of a list of items describing a position
  * among a (possibly infinite) parallel composition, followed
  * by a choice in a (possibly infinite) branching conditional.
  *
  * In the process (A | !_i B(i) | C), actions of A have parallel
  * choice 0, actions of C have parallel choice 2, and those of B
  * have parallel choice (1,i) which will later be instantiated to
  * (1,i_1), (1,i_2), etc.
  *
  * Then, in a process (if cond then P else Q), the branching position 0
  * will denote a success of the conditional, while 1 will denote a failure.
  * Finally, in (find i such that ... in ..) the indexed position (0,i)
  * will correspond to the success branches. *)

type 'a item = {
  par_choice : int * 'a ;
  sum_choice : int * 'a
}

type 'a t = ('a item) list

(** Actions are lists of items where infinite choices are represented
  * by index lists. *)
type action = (Vars.index list) t

(** Shapes represent classes of actions differing only in their indices:
  * they are obtained by replacing lists of indices by their lengths. *)
type shape = int t

(** [depends a b] test if [a] must occur before [b] as far
    as the control-flow is concerned -- it does not (cannot)
    take messages into account. It is not reflexive. *)
val depends : 'a t -> 'a t -> bool

(** [get_shape a] extracts the shape of an action *)
val get_shape : action -> shape

(** [same_shape a b] returns [Some subst] if [a] and [b] have the same action
    shapes. Return [None] otherwise.
    If [a] indices appear at most once in [a], then [subst] is the index
    substitution sending [a] to [b]. *)
val same_shape : action -> action -> Term.subst option

(** Convert action to the corresponding [TName] timestamp term. *)
val to_term : action -> Term.timestamp

(** Convert [TName] parameters to an action. *)
val of_term : Symbols.action Symbols.t -> Vars.index list -> action

(** Get dummy action of some length. Guarantees that a symbol exists for it. *)
val dummy_action : int -> action


(** {2 Action symbols}
  *
  * Action symbols are used to refer to actions in a concise manner. *)

(** Action symbols are associated to a list of indices and an action
  * using these indices, which represents a function from indices to
  * actions. *)

val fresh_symbol : string -> Symbols.Action.ns Symbols.t
val define_symbol :
  Symbols.Action.ns Symbols.t ->
  Vars.index list -> action -> unit
val find_symbol : string -> Vars.index list * action
val of_symbol : Symbols.Action.ns Symbols.t -> Vars.index list * action

(** {2 Action descriptions}
  *
  * Describe the behavior of an action: it consists of an input, followed by a
  * condition, then state updates and an output. *)


(** Type of action descriptions. *)
type descr = {
  action : action ;
  input : Channel.t * string ;
  indices : Vars.index list ;
  condition : Vars.index list * Term.formula ;
  updates : (Term.state * Term.message) list ;
  output : Channel.t * Term.message
}

(** Currently the user can only specify one bi-system,
  * hence system identifiers coincide with [Term.projection],
  * but (unlike [Term.projection]) they may be generalized in the future. *)


(** Given a set of actions and a projection, one can consider a specific
   bi-process or process, called a base system. *)
type system_name = string

val default_system_name : string

type base_system =
  { projection : Term.projection;
    id : system_name
  }

val make_base_system : Term.projection -> system_name -> base_system


(** Given two base systems, one can define the resulting bi-process,
    which can also be projected. This is our generic notion of system. *)

type system = private
  {
    projection : Term.projection;
    left  : base_system;
    right : base_system;
  }

val set_projection : Term.projection -> system -> system

val make_equiv_system : base_system -> base_system -> system

val make_default_system : Term.projection -> system_name -> system

val make_trace_system : base_system -> system

(** [pi_descr s a] returns the projection of the description. *)
val pi_descr : Term.projection -> descr -> descr

(** [get_descr a] returns the description corresponding to the action [a] in the
   [system].  Raise Not_found if no action corresponds to [a]. *)
val get_descr : system -> action -> descr

(** Iterate over all action descriptions in [system].
  * Only one representative of each action shape will be passed
  * to the function, with indices that are not guaranteed to be fresh. *)
val iter_descrs : system -> (descr -> unit) -> unit

(** {2 Registration of actions} *)

(** Specify if a given system name is not already in use. *)
val is_fresh : system_name -> bool

(** Register a new action symbol, action, and description, linked together. The
   set of registered actions for this system name will define the protocol under
   study. *)
val register : system_name ->
  Symbols.action Symbols.t -> Vars.index list -> action -> descr -> unit

(** Reset all action definitions done through [register]. *)
val reset : unit -> unit


(** {2 Pretty-printing} *)

(** Format an action, displayed through its structure. *)
val pp_action_structure : Format.formatter -> action -> unit

(** Format an action, displayed through its symbol. *)
val pp_action : Format.formatter -> action -> unit

(** Alias for [pp_action]. *)
val pp : Format.formatter -> action -> unit

(** Formatter for descriptions. *)
val pp_descr : Format.formatter -> descr -> unit

(** Formatter for actions shapes. *)
val pp_shape : Format.formatter -> shape -> unit

(** Formatter for parsed actions. *)
val pp_parsed_action : Format.formatter -> (string list) item list -> unit

(** Pretty-print all actions. *)
val pp_actions : Format.formatter -> unit -> unit

(** Pretty-print all action descriptions. *)
val pp_descrs : Format.formatter -> system -> unit -> unit

(** {2 Substitution} *)

(** Apply a term substitution to an action's indices. *)
val subst_action : Term.subst -> action -> action

(** Apply a substitution to a description. *)
val subst_descr : Term.subst -> descr -> descr
