(** Definition of a general sequent data-type,
  * which covers both local and global sequents
  * (and thus equivalence sequents).
  *
  * A sequent is made of:
  * - a set of hypotheses;
  * - a goal formula;
  * - an environment containing the sequent free variables.
  *
  * The signature defined here does not include functionalities
  * relying on the list of the already proved goals, to avoid
  * any dependency on {!Prover}. Such functionalities will be
  * added in {!Sequent}. *)

module L = Location

module SE = SystemExpr

module TraceHyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
(** {2 Module type for sequents} *)
(*------------------------------------------------------------------*)
module type S = sig

  type t
  type sequent = t
  type sequents = sequent list

  val pp     :             Format.formatter -> t -> unit
  val _pp    : dbg:bool -> Format.formatter -> t -> unit
  val pp_dbg :             Format.formatter -> t -> unit

  (*------------------------------------------------------------------*)

  (** Type of formulas used for sequent hypotheses. *)
  type hyp_form

  (** Type of formulas used for sequent conclusions. *)
  type conc_form

  (** The kinds of hypothesis and conclusion formulas. *)

  val hyp_kind : hyp_form Equiv.f_kind
  val conc_kind : conc_form Equiv.f_kind

  (*------------------------------------------------------------------*)
  (** default variable information of the sequent *)
  val var_info : Vars.Tag.t

  (*------------------------------------------------------------------*)
  module Hyps : Hyps.S1 with type hyp = hyp_form and type hyps := t

  (** {2 Access to sequent components}
    *
    * Each sequent consist of
    * a system, table, environment, type variables,
    * goal formula, and hypotheses. *)

  val env : t -> Env.t
  val set_env : Env.t -> t -> t

  val vars : t -> Vars.env
  val set_vars : Vars.env -> t -> t

  val goal : t -> conc_form
  val set_goal : conc_form -> t -> t

  val system : t -> SystemExpr.context

  (** Change the context of a sequent and its conclusion at the same time.
      The new conclusion is understood in the new context.
      The new context must be compatible with the old one.

      Hypotheses of the returned sequent (understood wrt the new context)
      are logical consequences of hypotheses of the original sequent
      (understood wrt its own context): some hypotheses will thus be dropped
      while others will be projected.

      The optional [update_local] function can be used to override the
      treatment of local hypotheses, i.e. to determine when they can be
      kept (possibly with modifications) or if they should be dropped. *)
  val set_goal_in_context :
    ?update_local:(Term.term -> Term.term option) ->
    SystemExpr.context -> conc_form -> t -> t

  val table : t -> Symbols.table
  val set_table : Symbols.table -> t -> t

  val ty_vars : t -> Type.tvars

  (*------------------------------------------------------------------*) 
  (** {2 Manipulation of bi-frame elements}
    *
    * These functionalities only make sense for equivalence sequents. *)

  val mem_felem    : int -> t -> bool
  val change_felem : ?loc:L.t -> int -> Term.term list -> t -> t
  val get_felem    : ?loc:L.t -> int -> t -> Term.term

  (*------------------------------------------------------------------*) 
  (** {2 Automated reasoning} *)

  val query_happens : precise:bool -> t -> Term.term -> bool

  (** Returns trace context, corresponding to [s.env.system.set] for
      both kinds of sequents. 
      Option projections to restrict the systems considered. *)
  val mk_trace_cntxt : ?se:SE.fset -> t -> Constr.trace_cntxt

  val get_trace_hyps : t -> TraceHyps.hyps

  (** [get_models s] returns a set of minimal models corresponding to the
      trace atoms in the sequent [s].
      See module {!Constr}.
      @raise Tactics.Tactic_hard_failure
         with parameter {!Tactics.TacTimeout} in case of timeout. *)
  val get_models : t -> Constr.models

  (*------------------------------------------------------------------*) 
  (** {2 Substitution} *)

  (** [subst subst s] returns the sequent [s] where the substitution has
      been applied to all hypotheses and the goal.
      It removes trivial equalities (e.g x=x). *)
  val subst : Term.subst -> t -> t

  (** [rename u v s] returns the sequent [s] where
      free variable u is replaced with v *)
  val rename : Vars.var -> Vars.var -> t -> t

  (*------------------------------------------------------------------*) 
  (** {2 Free variables} *)

  val fv : t -> Vars.Sv.t

  (*------------------------------------------------------------------*) 
  (** {2 Misc} *)

  val map : Equiv.Babel.mapper -> t -> t

  (** Smart constructors and destructors for hypotheses. *)
  module Hyp : SmartFO.S with type form = hyp_form

  (** Smart constructors and destructors for conclusions. *)
  module Conc : SmartFO.S with type form = conc_form
end

(*------------------------------------------------------------------*)
(** {2 Common utilities for sequent implementations} *)

(** Common setup for [set_goal_in_context].
    For each kind of hypothesis we need an update function that
    returns [None] if the hypothesis must be dropped, and [Some f]
    if it must be changed to [f].
    The [setup_set_goal_in_context] returns the pair of local and
    global update functions. *)
val setup_set_goal_in_context :
  old_context:SE.context ->
  new_context:SE.context ->
  table:Symbols.table ->
  vars:Vars.env ->
  ( Term.term ->  Term.term option) *
  (Equiv.form -> Equiv.form option)
