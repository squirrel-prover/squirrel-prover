(** Processes are decomposed as structured sets of actions. *)

open Vars

(** Indices are used to generate arbitrary families of terms *)
module Index : VarType

type index = Index.t

type 'a item = {
  par_choice : int * 'a ;
  sum_choice : int * 'a
}
type 'a t = ('a item) list

val conflict : 'a t -> 'a t -> bool

val depends : 'a t -> 'a t -> bool

val enables : 'a t -> 'a t -> bool

type action_shape = int t

type action = (index list) t

val mk_shape : int t -> action_shape

val get_shape : action -> action_shape

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
