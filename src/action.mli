(** Processes are decomposed as structured sets of actions. *)
open Vars

(** Indices are used to generate arbitrary families of terms, and thus duplicate
    of actions *)
module Index : VarType

type index = Index.t

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
type action = (index list) t

(** [get_shape a] extracts the action_shape of an action *)
val get_shape : action -> action_shape

(** [action_indices a] gives back all index appearing inside the action *)
val action_indices : action -> index list

(** Index variable substitutions *)
type isubst = (index*index) list

val pp_isubst : Format.formatter -> isubst -> unit

(** [same_shape a b] returns [Some subst] if [a] and [b] have the same action
    shapes. Return [None] otherwise.
    If [a] indices appear at most once in [a], then [subst] is the index
    substitution sending [a] to [b]. *)
val same_shape : action -> action -> isubst option

(** [constr_equal a b] returns the list of index constraints necessary to have
    [a] and [b] equal, if there is one. Return None otherwise. *)
val constr_equal : action -> action -> isubst option

(** Given an action, generate a fresh instance of it together with
  * the corresponding substitution for indices. *)
val refresh : action -> action * isubst

(** Formatter for actions. *)
val pp_action : Format.formatter -> action -> unit

(** Alias for [pp_action]. *)
val pp : Format.formatter -> action -> unit

(** Formatter for actions shapes. *)
val pp_action_shape : Format.formatter -> action_shape -> unit

(** Formatter for parsed actions. *)
val pp_parsed_action : Format.formatter -> (string list) item list -> unit

(** Action symbols *)

(** Action symbols are associated to a list of indices and an action
  * using these indices, which represents a function from indices to
  * actions. *)

val fresh_symbol : string -> (Index.t list * action) Symbols.t
val define_symbol :
  (Index.t list * action) Symbols.t ->
  Index.t list -> action -> unit
val find_symbol : string -> Index.t list * action
