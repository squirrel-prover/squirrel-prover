(** Actions are the basis of our internal semantics for protocols. *)

(** Actions uniquely describe execution points in a process.
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

(** The position of an action inside a process can be captured by a list of
    parallel and sum choices *)
type 'a t = ('a item) list

(** [conflict a b] checks whether two actions [a] and [b] are in conflict. *)
val conflict : 'a t -> 'a t -> bool

(** [depends a b] test if [a] must occur before [b] as far
    as the control-flow is concerned -- it does not (cannot)
    take messages into account. *)
val depends : 'a t -> 'a t -> bool

(** [enables a b] tests whether action [a] enables [b]. *)
val enables : 'a t -> 'a t -> bool

(** [action_shape] captures the position of an action inside a process, but not
    the potential index variables upon which it depends. It only captures the
    number of index variables defined at multiple places *)
type action_shape = int t

(** An [action] is an [action_shape] inside which all index variables are
    explicits. *)
type action = (Index.t list) t

(** [get_shape a] extracts the action_shape of an action *)
val get_shape : action -> action_shape

(** [action_indices a] gives back all index appearing inside the action *)
val action_indices : action -> Index.t list

(** [same_shape a b] returns [Some subst] if [a] and [b] have the same action
    shapes. Return [None] otherwise.
    If [a] indices appear at most once in [a], then [subst] is the index
    substitution sending [a] to [b]. *)
val same_shape : action -> action -> Index.subst option

(** [constr_equal a b] returns the list of index constraints necessary to have
    [a] and [b] equal, if there is one. Return None otherwise. *)
val constr_equal : action -> action -> Index.subst option

(** Format an action, displayed through its symbol. *)
val pp_action_structure : Format.formatter -> action -> unit

(** Format an action, displayed through its structure. *)
val pp_action : Format.formatter -> action -> unit

(** Alias for [pp_action]. *)
val pp : Format.formatter -> action -> unit

(** Formatter for actions shapes. *)
val pp_action_shape : Format.formatter -> action_shape -> unit

(** Formatter for parsed actions. *)
val pp_parsed_action : Format.formatter -> (string list) item list -> unit

val subst_action : Term.subst -> action -> action

(** Convert action to the corresponding [TName] timestamp term. *)
val to_term : action -> Term.timestamp

(** Convert [TName] parameters to an action. *)
val of_term : Symbols.action Symbols.t -> Index.t list -> action

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
  Index.t list -> action -> unit
val find_symbol : string -> Index.t list * action
val of_symbol : Symbols.Action.ns Symbols.t -> Index.t list * action

(** {2 Action descriptions}
  *
  * Describe the behavior of an action: it consists of an input, followed by a
  * condition, then state updates and an output. *)

(** Type action_descr *)
type action_descr = {
  action : action ;
  input : Channel.t * string ;
  indices : Index.t list ;
  condition : Index.t list * Bformula.fact ;
  updates : (Term.state * Term.term) list ;
  output : Channel.t * Term.term
}

(** Register a new action symbol, action, and description,
  * linked together. *)
val register : Symbols.action Symbols.t -> Index.t list -> action -> action_descr -> unit

(** Reset all action definitions. *)
val reset : unit -> unit

val pp_action_descr : Format.formatter -> action_descr -> unit

(** Iterate over a complete set of action descriptions.
    Does not instantiate fresh copies of the actions, as it increases
    unecessarily the variable counters. Can be used for display purposes. *)
val iter_csa : (action_descr -> unit) -> unit

(** [get_descr a] returns the description corresponding to the action [a].
    Raise Not_found if no action corresponds to [a]. *)
val get_action_descr : action -> action_descr

(** Pretty-print actions *)
val pp_actions : Format.formatter -> unit -> unit

(** Pretty-print action descriptions *)
val pp_action_descrs : Format.formatter -> unit -> unit

(** Pretty-print actions and action descriptions *)
val pp_proc : Format.formatter -> unit -> unit

(** Apply a substitution to a description. *)
val subst_action_descr : Term.subst -> action_descr -> action_descr
