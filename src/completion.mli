(** Completion of equalities and disequalities set *)

type state

val pp_state : Format.formatter -> state -> unit

(** [complete ?exn l] construct a complete term rewritting system from the set of
    equations inside l.
    - [exn] is thrown if the tactic timeout.
      Default to [Tactics.Tactic_hard_failure TacTimeout]. *)
val complete : 
  ?exn:exn -> Symbols.table -> Term.esubst list -> state 

(** [check_equalities s l] checks that all equalities inside [l] hold
    w.r.t [s] *)
val check_equalities : state -> (Term.term * Term.term) list -> bool

(** [check_disequalities s neqs l] checks that all disequalities inside [l]
    are implied by inequalities inside [neqs], wrt [s]. *)
val check_disequalities :
  state -> (Term.term * Term.term) list -> (Term.term * Term.term) list -> bool

(** [name_index_cnstrs state l] looks for all names that are equal w.r.t. the
    rewrite relation in [state], and add the corresponding index equalities.
    E.g., if [n[i,j]] and [n[k,l]] are equal, then the returned list
    would contain [i=k] and [j=l]. *)
val name_index_cnstrs :
  Symbols.table -> state -> Term.term list -> Term.term list

(** Print the set of rules in the initial TRS (e.g. dec(enc(x,y,r),y) -> x) *)
val print_init_trs : Format.formatter -> Symbols.table -> unit
