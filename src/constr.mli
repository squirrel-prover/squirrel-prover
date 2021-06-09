
(** The minimal models a of constraint.
    Here, minimanility means inclusion w.r.t. the predicates. *)
type models

type trace_literal = [`Pos | `Neg] * Term.trace_atom

type trace_literals = trace_literal list

(*------------------------------------------------------------------*) 
(** [models_conunct l] returns the list of minimal models of the conjunction of
    atoms. *)
val models_conjunct : trace_literals -> models Utils.timeout_r

val m_is_sat : models -> bool

(** [query models at] returns [true] if the conjunction of the atoms in [ats]
    is always true in [models].
    This is an under-approximation (i.e. correct but not complete).
    Because we under-approximate, we are very unprecise on dis-equalities
    (i.e. atoms of the form [(Neq,_,_)]). *)
val query : precise:bool -> models -> trace_literal list -> bool

(** [maximal_elems models elems] computes a set of elements which contains
    the maximal elements of [elems] in every model in [models].
    This can only be over-approximated, and our result may not be the best.
    This function may be non-deterministic. *)
val maximal_elems : 
  precise:bool -> models -> Term.timestamp list -> Term.timestamp list

(** [get_ts_equalities models ts], given a list of models [models] and a list
    of timespoints [ts], gives back the classes for equality in all models. *)
val get_ts_equalities : 
  precise:bool -> models -> Term.timestamp list -> Term.timestamp list list

val get_ind_equalities : 
  precise:bool -> models -> Vars.index list -> Vars.index list list

(** [find_eq_action models t] looks for an action [ts] equal to [t]. *)
val find_eq_action : models -> Term.timestamp -> Term.timestamp option

(*------------------------------------------------------------------*)
(** Context of a trace model. *)
type trace_cntxt = {
  table  : Symbols.table;
  system : SystemExpr.t;

  (* used to find an action occuring at a given timestamp *)
  models : models option;
}
