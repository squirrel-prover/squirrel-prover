(** Definition of a general sequent data-type,
  * which covers both reachability and general sequents
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

(*------------------------------------------------------------------*)

(** Sequent kinds. *)
type _ s_kind =
  | KReach : Term.message s_kind
  | KEquiv :   Equiv.form s_kind

(*------------------------------------------------------------------*)
(** {2 Module type for sequents} *)

module type S = sig
  type t
  type sequent = t
  type sequents = sequent list

  val pp : Format.formatter -> t -> unit

  (*------------------------------------------------------------------*)
  (** Type of formulas, used for hypotheses and goals.
    * It is actually constrained to be {!Term.message}
    * or {!Equiv.form}, due to {!LowSequent.S.s_kind} below. *)
  type form

  val pp_form : Format.formatter -> form -> unit

  (*------------------------------------------------------------------*)
  (** The kind of the sequent: allows type introspection. *)
  val s_kind : form s_kind

  (*------------------------------------------------------------------*)
  module Hyps : Hyps.HypsSeq with type hyp = form and type sequent = t

  val reach_to_form : Term.message -> form
  val form_to_reach : ?loc:Location.t -> form -> Term.message
  val gform_of_form : form -> Equiv.gform

  (** {2 Access to sequent components}
    *
    * Each sequent consist of
    * a system, table, environment, type variables,
    * goal formula, and hypotheses. *)

  val env : t -> Vars.env
  val set_env : Vars.env -> t -> t

  val goal : t -> form
  val set_goal : form -> t -> t
  val set_reach_goal : Term.message -> t -> t

  val system : t -> SystemExpr.system_expr
  val set_system : SystemExpr.system_expr -> t -> t

  val table : t -> Symbols.table
  val set_table : Symbols.table -> t -> t

  val ty_vars : t -> Type.tvars

  (** {2 Manipulation of bi-frame elements}
    *
    * These functionalities only make sense for equivalence sequents. *)

  val mem_felem    : int -> t -> bool
  val change_felem : int -> Term.message list -> t -> t
  val get_felem    : int -> t -> Term.message

  (** {2 Automated reasoning} *)

  val query_happens : precise:bool -> t -> Term.timestamp -> bool

  val mk_trace_cntxt : t -> Constr.trace_cntxt

  val get_trace_literals : t -> Term.trace_literal list

  val get_hint_db : t -> Hint.hint_db

  (** [get_models s] returns a set of minimal models corresponding to the
    * trace atoms in the sequent [s].
    * See module {!Constr}.
    * @raise Tactics.Tactic_hard_failure
    *        with parameter {!Tactics.TacTimeout} in case of timeout. *)
  val get_models : t -> Constr.models

  (** {2 Substitution} *)

  (** [subst subst s] returns the sequent [s] where the substitution has
      been applied to all hypotheses and the goal.
      It removes trivial equalities (e.g x=x). *)
  val subst     : Term.subst ->   t ->   t
  val subst_hyp : Term.subst -> form -> form

  (** {2 Free variables} *)

  val fv_form : form -> Vars.Sv.t
  val fv      : t    -> Vars.Sv.t

  (** {2 Misc} *)

  (** Get (some) terms appearing in an hypothesis.
    * For instance, terms occurring under binders may not be included. *)
  val get_terms : form -> Term.message list

  val map : (form -> form) -> t -> t

  (** Matching. *)
  module Match : Term.MatchS with type t = form

  (** Smart constructors and destructors. *)
  module Smart : Term.SmartFO with type form = form

end
