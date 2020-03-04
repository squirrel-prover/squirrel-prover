type elem =
  | Formula of Term.formula
  | Message of Term.message

type t
type sequent = t

val init : Vars.env -> elem list -> t

val pp : Format.formatter -> t -> unit

val pp_init : Format.formatter -> t -> unit

val id_left : sequent -> Action.system_id
val id_right : sequent -> Action.system_id

val get_env : t -> Vars.env
val set_env : Vars.env -> t -> t

val get_systems : t -> Term.projection * Term.projection

(** Get the list of biterms describing the two frames. *)
val get_biframe : t -> elem list

(** Return a new equivalence judgment with the given biframe. *)
val set_biframe : t -> elem list -> t

(** Get the list of biterms describing the hypothesis frames. *)
val get_hypothesis_biframe : t -> elem list

(** Return a new equivalence judgment with the given hypothesis biframe. *)
val set_hypothesis_biframe : t -> elem list -> t

(** Get one of the projections of the biframe,
  * as a list of terms where diff operators have been fully
  * eliminated. *)
val get_frame : Term.projection -> t -> elem list

(** Project a biterm of the frame to one side. *)
val pi_elem : Term.projection -> elem -> elem

(** [apply_subst_frame subst f] returns the frame [f] where the substitution has
   been applied to all terms. *)
val apply_subst_frame : Term.subst -> elem list -> elem list

(** [apply_subst subst s] returns the sequent [s] where the substitution has
   been applied to its conclusion and hypothesis. *)
val apply_subst : Term.subst -> t -> t
