(** Completion of equalities and disequalities set *)

type state

val pp_state : Format.formatter -> state -> unit

(** [complete ?exn l] constructs a complete term rewriting system
    from the set of equations inside [l].
    - [exn] is thrown if the tactic runs out of time.
      Defaults to [Tactics.Tactic_hard_failure TacTimeout]. *)
val complete :
  ?exn:exn -> Symbols.table -> Term.esubst list -> state

(** [check_equalities s l] checks that all equalities inside [l] hold
    wrt [s] *)
val check_equalities : state -> (Term.term * Term.term) list -> bool

(** [check_disequalities s neqs l] checks that all disequalities inside [l]
    are implied by inequalities inside [neqs], wrt [s]. *)
val check_disequalities :
  state -> (Term.term * Term.term) list -> (Term.term * Term.term) list -> bool

(** [name_index_cnstrs state l] looks for all [large] names that are equal
    w.r.t. the rewrite relation in [state], and returns the
    corresponding equalities.
    E.g., if [n(i,j)] and [m(k,l)] are equal, then the returned list
    will contain [(n, \[i;k\]), (m, \[j;l\])]. *)
val name_index_cnstrs :
  Symbols.table -> state -> Term.term list ->
  ((Symbols.name * Term.term list) * (Symbols.name * Term.term list)) list

(** Print the set of rules in the initial TRS (e.g. dec(enc(x,y,r),y) -> x). *)
val print_init_trs : Format.formatter -> Symbols.table -> unit
