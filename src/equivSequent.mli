type elem =
  | Formula of Term.formula
  | Message of Term.message

type t
type sequent = t

val pp : Format.formatter -> t -> unit

val get_env : t -> Vars.env

val get_left_frame : t -> elem list
val get_right_frame : t -> elem list
