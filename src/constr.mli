module SE = SystemExpr

(*------------------------------------------------------------------*)
(** The minimal models a of constraint.
    Here, minimality means inclusion w.r.t. the predicates. *)
type models

(*------------------------------------------------------------------*)
(** [models_conunct ?exn l] returns the list of minimal models of 
    the conjunction of atoms.
    - [exn] is thrown if the tactic timeout.
      Default to [Tactics.Tactic_hard_failure TacTimeout]. *)
val models_conjunct : int -> ?exn:exn -> Term.terms -> models 

val m_is_sat : models -> bool

(** [query models at] returns [true] if the conjunction of the atoms in [ats]
    is always true in [models].
    This is an under-approximation (i.e. correct but not complete).
    Because we under-approximate, we are very unprecise on dis-equalities
    (i.e. atoms of the form [(Neq,_,_)]). *)
val query : precise:bool -> models -> Term.Lit.literals -> bool

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

val get_ind_equalities :
  precise:bool -> models -> Vars.vars -> Vars.vars list

(** [find_eq_action models t] looks for an action [ts] equal to [t]. *)
val find_eq_action : models -> Term.term -> Term.term option

(*------------------------------------------------------------------*)
(** Context of a trace model. *)
type trace_cntxt = {
  table  : Symbols.table;
  system : SystemExpr.fset;
  models : models option;
  (** used to find an action occurring at a given timestamp *)
}

(** Create context with undefined models. *)
val make_context :
  table:Symbols.table ->
  system:SystemExpr.fset ->
  trace_cntxt
