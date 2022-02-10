(** Equivalence sequents,
  * or more accurately global sequents whose conclusion
  * is a global meta-formula. *)

(*------------------------------------------------------------------*)
include LowSequent.S with
  type  hyp_form = Equiv.global_form and
  type conc_form = Equiv.global_form

(*------------------------------------------------------------------*)
(** {2 Creation of global sequents} *)

(** Initialize a sequent with the given components.
  * At most one hypothesis can be given, which will be named "H":
  * this is intended to ease simple cases like observational
  * equivalence goals.
  * For more general cases, the global meta-formula used as conclusion
  * can include implications. *)
val init : 
  system:SystemExpr.t ->
  table:Symbols.table ->
  hint_db:Hint.hint_db ->
  ty_vars:Type.tvars ->
  env:Vars.env ->
  ?hyp:Equiv.form ->
  Equiv.form ->
  t

(** Special pretty-printer for initial sequents.
  * It does not display hypotheses, which might be misleading. *)
val pp_init : Format.formatter -> t -> unit

(*------------------------------------------------------------------*)
(** {2 Utilities for equivalence sequents}
  * Equivalence sequents are global sequents whose conclusion
  * is an equivalence atom. *)

val set_equiv_goal : Equiv.equiv -> t -> t

(** Get one of the projections of the biframe,
  * as a list of terms where diff operators have been fully
  * eliminated.
  * @return [None] if the conclusion is not an equivalence atom. *)
val get_frame : Term.projection -> t -> Equiv.equiv option

val goal_is_equiv : t -> bool

val goal_as_equiv : t -> Equiv.equiv

(*------------------------------------------------------------------*)
(** {2 Trace sequents and reachability goals} *)

(** Change sequent goal to some reachability atom. *)
val set_reach_goal : Term.message -> t -> t

(** Convert a global sequent whose conclusion is a reachability
  * atom to a trace sequent.
  * @raise Tactics.soft_failure if sequent conclusion is not well-formed. *)
val to_trace_sequent : t -> LowTraceSequent.t

(*------------------------------------------------------------------*)
(** {2 Automated reasoning} *)

val query_happens : precise:bool -> t -> Term.timestamp -> bool
