(** Completion of equalities and disequalities set *)

type state

val pp_state : Format.formatter -> state -> unit

(** [complete l] construct a complete term rewritting system from the set of
    equations inside l.
    May timeout. *)
val complete : 
  Symbols.table -> Term.esubst list -> state Utils.timeout_r

(** [check_equalities s l] checks that all equalities inside [l] hold
    w.r.t [s] *)
val check_equalities : state -> Term.esubst list -> bool

(** [name_index_cnstrs state l] looks for all names that are equal w.r.t. the
    rewrite relation in [state], and add the corresponding index equalities.
    E.g., if [n[i,j]] and [n[k,l]] are equal, then the returned list
    would contain [i=k] and [j=l]. *)
val name_index_cnstrs :
  Symbols.table -> state -> Term.message list -> Term.message list

(** [name_indep_cnstrs state l] looks for all name equals to a Term.message 
    w.r.t. the rewrite relation in [state], and adds the fact that the name must 
    be equal to one of the name appearing inside the Term.message. *)
val name_indep_cnstrs :
  Symbols.table -> state -> Term.message list -> Term.message list

(** Print the set of rules in the initial TRS (e.g. dec(enc(x,y,r),y) -> x) *)
val print_init_trs : Format.formatter -> Symbols.table -> unit
