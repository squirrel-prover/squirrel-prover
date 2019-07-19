open Term

type state

val complete : (term * term) list -> state

val check_disequalities : state -> (term * term) list -> bool

val check_equalities : state -> (term * term) list -> bool
