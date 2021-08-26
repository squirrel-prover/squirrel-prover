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

val get_indices : action -> Vars.index list

val fv_action : action -> Vars.Sv.t

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

(** Convert [Action] parameters to an action. *)
val of_term :
  Symbols.action Symbols.t -> Vars.index list ->
  Symbols.table ->
  action

(** Return a dummy action of a given shape. *)
val dummy : shape -> action

(*------------------------------------------------------------------*)
(** {2 Action symbols}
  *
  * Action symbols are used to refer to actions in a concise manner.
  * They are indexed and are associated to an action using the argument
  * indices. *)

type Symbols.data += Data of Vars.index list * action

(** Get a fresh symbol whose name starts with the given prefix.
    If [exact] is true, the symbol must be exactly the argument. *)
val fresh_symbol :
  Symbols.table -> exact:bool -> Symbols.lsymb ->
  Symbols.table * Symbols.action Symbols.t

val define_symbol :
  Symbols.table ->
  Symbols.Action.ns Symbols.t -> Vars.index list -> action ->
  Symbols.table

val find_symbol : Symbols.lsymb -> Symbols.table -> Vars.index list * action

val of_symbol :
  Symbols.action Symbols.t -> Symbols.table ->
  Vars.index list * action

val arity : Symbols.action Symbols.t -> Symbols.table -> int

(*------------------------------------------------------------------*)
(** {2 Action descriptions}
  *
  * Describe the behavior of an action: it consists of an input, followed by a
  * condition, then state updates and an output. *)

(** Type of action descriptions. *)
type descr = {
  name      : Symbols.action Symbols.t ;
  action    : action ;
  input     : Channel.t * string ;
  indices   : Vars.index list ;
  condition : Vars.index list * Term.message ;
  updates   : (Term.state * Term.message) list ;
  output    : Channel.t * Term.message;
  globals : Symbols.macro Symbols.t list;
}

(** [pi_descr s a] returns the projection of the description. As descriptions
   are only obtained for a system, one can when this system is without
   projection, validly project to obtain the left or the right descriptions,
   that in fact corresponds to the left or the right base_sytem projection of
   the action.  *)
val pi_descr : Term.projection -> descr -> descr

(** Refresh (globally) binded variables in a description. *)
val refresh_descr : descr -> descr

(*------------------------------------------------------------------*)
(** {2 Pretty-printing} *)

(** Format an action, displayed through its structure. *)
val pp_action_structure : Format.formatter -> action -> unit

(** Format the action name of an action description. *)
val pp_descr_short : Format.formatter -> descr -> unit

(** Formatter for descriptions. *)
val pp_descr : Format.formatter -> descr -> unit

(** Formatter for actions shapes. *)
val pp_shape : Format.formatter -> shape -> unit

(** Formatter for parsed actions. *)
val pp_parsed_action : Format.formatter -> (string list) item list -> unit

(** Pretty-print all actions. *)
val pp_actions : Format.formatter -> Symbols.table -> unit


(*------------------------------------------------------------------*)
(** {2 Substitution} *)

(** Apply a term substitution to an action's indices. *)
val subst_action : Term.subst -> action -> action

(** Apply a substitution to a description. *)
val subst_descr : Term.subst -> descr -> descr


(*------------------------------------------------------------------*)
(** {2 FA-DUP } *)

(** [is_dup is_eq t terms] check if:
    - [t] appears twice in [terms];
    - or if [t] is [input\@t] with [frame\@t'] appearing in [terms] 
      where [pred(t) <= t'];
    - or if [t] is [exec\@t] with [frame\@t'] appearing in [terms] 
      where with [t <= t']. *)
val is_dup : 
  Symbols.table -> Term.message -> Term.message list 
  -> bool

(** Same as [is_dup], but instead of checking term equality, checks 
    that term matchs. *)
val is_dup_match : 
  (Term.eterm -> Term.eterm -> 'a -> 'a option) -> 'a ->
  Symbols.table -> Term.message -> Term.message list 
  -> 'a option
