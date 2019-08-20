open Term

type state

val complete : (term * term) list -> state

val check_disequalities : state -> (term * term) list -> bool

val check_equalities : state -> (term * term) list -> bool


(** [name_index_cnstrs state l] looks for all names that are equal w.r.t. the
    rewrite relation in [state], and add the corresponding index equalities.
    E.g., if n[i,j] and n[k,l] are equal, then i = k and j = l.*)
val name_index_cnstrs : state -> term list -> tatom bformula list

(** [constant_index_cnstrs] is the same as [name_index_cnstrs], but for
    constant function symbols equalities. *)
val constant_index_cnstrs : fname -> state -> term list -> tatom bformula list
