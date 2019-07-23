(** The minimal models a of constraint.
    Here, minimanility means inclusion w.r.t. the predicates. *)
type models

(** [models l] returns the list of minimal models of a constraint. *)
val models : Term.constr -> models

val is_sat : Term.constr -> bool
val m_is_sat : models -> bool

(** [query models at] returns [true] if the conjunction of the atoms in [ats]
    is always true in [models].
    This is an under-approximation (i.e. correct but not complete).
    Because we under-approximate, we are very unprecise on dis-equalities
    (i.e. atoms of the form [(Neq,_,_)]). *)
val query : models -> Term.tatom list -> bool
