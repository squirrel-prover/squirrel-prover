type elem =
  | Formula of Term.formula
  | Message of Term.message

type t
type sequent = t

val init : Vars.env -> elem list -> t

val pp : Format.formatter -> t -> unit

val pp_init : Format.formatter -> t -> unit

val get_env : t -> Vars.env

val get_systems : t -> Term.projection * Term.projection

(** Get the list of biterms describing the two frames. *)
val get_biframe : t -> elem list

(** Return a new equivalence judgment with the given biframe. *)
val set_biframe : t -> elem list -> t

(** Get one of the projections of the biframe,
  * as a list of terms where diff operators have been fully
  * eliminated. *)
val get_frame : Term.projection -> t -> elem list
