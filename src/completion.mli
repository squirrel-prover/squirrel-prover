(** Completion of equalities and disequalities set *)

type state

(** [complete l] construct a complete term rewritting system from the set of
    equations inside l *)
val complete : (Term.message * Term.message) list -> state

(** [check_disequalities s neqs l] checks that all disequalities inside [l] are
    implied by inequalities inside neqs, w.r.t [s]. *)
val check_disequalities : state ->  (Term.message * Term.message) list
  -> (Term.message * Term.message) list -> bool

(** [check_equalities s l] checks that all equalities inside [l] hold
    w.r.t [s] *)
val check_equalities : state -> (Term.message * Term.message) list -> bool

(** [name_index_cnstrs state l] looks for all names that are equal w.r.t. the
    rewrite relation in [state], and add the corresponding index equalities.
    E.g., if [n[i,j]] and [n[k,l]] are equal, then the returned list
    would contain [i=k] and [j=l]. *)
val name_index_cnstrs :
  state -> Term.message list -> Formula.formula list

(** [name_indep_cnstrs state l] looks for all name equals to a Term.message w.r.t. the
    rewrite relation in [state], and adds the fact that the name must be equal
    to one of the name appearing inside the Term.message. *)
val name_indep_cnstrs : state -> Term.message list -> Formula.formula list
