type models

(** [models l] returns the list of "minimal models" of a constraint. *)
val models : Term.constr -> models

val is_sat : Term.constr -> bool
val m_is_sat : models -> bool
