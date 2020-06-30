(** Actions are the basis of our internal semantics for protocols.
  * In the theory, an action is an indexed symbol with a semantics
  * (given through conditional, update and output terms) and
  * actions are equipped with a sequential dependency relation
  * (and perhaps a conflict relation). Things are a bit different
  * in the implementation:
  *  - Type [action] below refers to execution points, which yield
  *    dependency and conflict relations. Execution points are one
  *    possible implementation of our abstract notion of action,
  *    that is convenient for our translation from the applied
  *    pi-calculus.
  *  - We associate to each such action an "action description"
  *    (type [descr]) which carries the semantics of the action.
  *  - Finally, we have action symbols (type [Symbols.action Symbols.t]).
  *
  * Our prover allows to declare and reason about several systems.
  * Actions and symbols exist independently of a system, but descriptions
  * are given relative to a (bi)system. *)

(** {2 Execution points}
  *
  * Actions uniquely describe execution points in a protocol.
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

(** Distance in control-flow graph:
  * [Some d] is returned when [a <= b] and they are at distance
  * [d] from each other in the graph (distance is zero when [a = b]);
  * [None] is returned when it is not the case that [a <= b]. *)
val distance : 'a t -> 'a t -> int option

(** [get_shape a] extracts the shape of an action *)
val get_shape : action -> shape

(** [same_shape a b] returns [Some subst] if [a] and [b] have the same action
    shapes. Return [None] otherwise.
    If [a] indices appear at most once in [a], then [subst] is the index
    substitution sending [a] to [b]. *)
val same_shape : action -> action -> Term.subst option

(** Convert action to the corresponding [Action] timestamp term. *)
val to_term : action -> Term.timestamp

(** Convert [Action] parameters to an action. *)
val of_term : Symbols.action Symbols.t -> Vars.index list -> action

(** Get dummy action of some length. Guarantees that a symbol exists for it. *)
val dummy_action : int -> action


(** {2 Action symbols}
  *
  * Action symbols are used to refer to actions in a concise manner.
  * They are indexed and are associated to an action using the argument
  * indices. *)

(** Get a fresh symbol whose name starts with the given prefix. *)
val fresh_symbol :
  Symbols.table -> string -> Symbols.table * Symbols.action Symbols.t

val find_symbol : string -> Vars.index list * action

val of_symbol : Symbols.action Symbols.t -> Vars.index list * action

(** {2 Systems} *)

(** The user specifies one or more (bi)systems, identified using names.
  * Each (bi)system is a set of (bi)actions, obtained from a (bi)process. *)

type system_name = string

val default_system_name : string

(** A single system, that is a system without diff, is given by the name of a
   (bi)system , and either Left or Right. *)

type single_system =
  | Left of system_name
  | Right of system_name


val get_proj : single_system -> Term.projection

(* A system defines either a system without diff, or a system with diff.  It can
   be obtained from:
    - a single system;
    - a system obtained from a system name,
   as it was declared, considered with its diff terms;
    - a system obtained by
   combinaison of two single system, one for the left and one for the right. *)
type system =
  | Single of single_system
  | SimplePair of system_name
  | Pair of single_system * single_system

val pp_system : Format.formatter -> system -> unit


(** Prject a system according to the given projection.  The pojection must not
   be None, and the system must be a bi system, i.e either SimplePair or Pair.
   *)
val project_system : Term.projection -> system -> system

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

(** [pi_descr s a] returns the projection of the description. As descriptions
   are only obtained for a system, one can when this system is without
   projection, validly project to obtain the left or the right descriptions,
   that in fact corresponds to the left or the right base_sytem projection of
   the action.  *)
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

(** Register an action symbol in a system,
  * associating it with an action description.
  * The set of registered actions for this system name will define
  * the protocol under study.
  * Returns the updated table and the actual action symbol used
  * (currently the proposed symbol may not be used for technical
  * reasons that will eventually disappear TODO). *)
val register :
  Symbols.table -> system_name ->
  Symbols.action Symbols.t -> Vars.index list ->
  action -> descr -> Symbols.table * Symbols.action Symbols.t

(** Reset all action definitions done through [register]. *)
val reset : unit -> unit


type esubst_descr =
  | Condition of Term.formula * action
  | Output of Term.message * action

type subst_descr = esubst_descr list

exception SystemNotFresh

val clone_system_subst : system -> system_name -> subst_descr -> unit

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
val pp_descrs : Format.formatter -> system -> unit

(** {2 Substitution} *)

(** Apply a term substitution to an action's indices. *)
val subst_action : Term.subst -> action -> action

(** Apply a substitution to a description. *)
val subst_descr : Term.subst -> descr -> descr
