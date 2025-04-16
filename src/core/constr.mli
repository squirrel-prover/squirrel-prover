module SE = SystemExpr

(*------------------------------------------------------------------*)
(** The minimal models a of constraint.
    Here, minimality means inclusion w.r.t. the predicates. *)

type models 

(*------------------------------------------------------------------*)

val empty_model : models

(** [empty_models m] returns true when there is in fact no model. *)
val empty_models : models -> bool


(** [models_conjunct max ?exn l] returns the list of minimal models of
    the conjunction of atoms, if this can be computed in less than [max]
    seconds.
    - [exn] is thrown if the tactic runs out of time.
      Default to [Tactics.Tactic_hard_failure TacTimeout]. *)
val models_conjunct :
  ?exn:exn -> timeout:int ->
  ?allow_disjunction:bool ->
  table:Symbols.table -> Term.terms -> models 

val m_is_sat : models -> bool

(** [is_tautology max ?exn t] check whether [t] is a tautology.
    The [max] and [exn] paramaters have the same meaning as in
    [models_conjunct].  *)
val is_tautology :
  ?exn:exn -> timeout:int ->
  ?allow_disjunction:bool ->
  table:Symbols.table -> Term.term -> bool

(** [query models at] returns [true] if the conjunction of the atoms in [ats]
    is always true in [models].
    This is an under-approximation (i.e. correct but not complete).
    Because we under-approximate, we are very imprecise on disequalities
    (i.e. atoms of the form [(Neq,_,_)]). *)
val query : precise:bool -> models -> Term.terms -> bool

(** [maximal_elems models elems] computes a set of elements which contains
    the maximal elements of [elems] in every model in [models].
    This can only be over-approximated, and our result may not be the best.
    This function may be non-deterministic. *)
val maximal_elems :
  precise:bool -> models -> Term.terms -> Term.terms

(** [get_ts_equalities models ts], given a list of models [models] and a list
    of timespoints [ts], gives back the classes for equality in all models. *)
val get_ts_equalities :
  precise:bool -> models -> Term.terms -> Term.terms list

(** [find_eq_action models t] looks for an action [ts] equal to [t]. *)
val find_eq_action : models -> Term.term -> Term.term option
