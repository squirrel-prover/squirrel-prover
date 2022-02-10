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

(** {2 Module type for sequents} *)

module L = Location

module type S = sig

  type t
  type sequent = t
  type sequents = sequent list

  val pp : Format.formatter -> t -> unit

  (*------------------------------------------------------------------*)

  (** Type of formulas used for sequent hypotheses. *)
  type hyp_form

  (** Type of formulas used for sequent conclusions. *)
  type conc_form

  (** The kinds of hypothesis and conclusion formulas. *)

  val hyp_kind : hyp_form Equiv.f_kind
  val conc_kind : conc_form Equiv.f_kind

  (* val pp_hyp  : Format.formatter -> hyp_form  -> unit
  val pp_conc : Format.formatter -> conc_form -> unit *)

  (*------------------------------------------------------------------*)
  module Hyps : Hyps.HypsSeq with type hyp = hyp_form and type sequent = t

  (** {2 Access to sequent components}
    *
    * Each sequent consist of
    * a system, table, environment, type variables,
    * goal formula, and hypotheses. *)

  val env : t -> Vars.env
  val set_env : Vars.env -> t -> t

  val goal : t -> conc_form
  val set_goal : conc_form -> t -> t

  val system : t -> SystemExpr.t
  val set_system : SystemExpr.t -> t -> t

  val table : t -> Symbols.table
  val set_table : Symbols.table -> t -> t

  val ty_vars : t -> Type.tvars

  (** {2 Manipulation of bi-frame elements}
    *
    * These functionalities only make sense for equivalence sequents. *)

  val mem_felem    : int -> t -> bool
  val change_felem : ?loc:L.t -> int -> Term.message list -> t -> t
  val get_felem    : ?loc:L.t -> int -> t -> Term.message

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
  val subst      : Term.subst -> t -> t

  (** {2 Free variables} *)

  val fv : t -> Vars.Sv.t

  (** {2 Misc} *)

  val map : Equiv.Babel.mapper -> t -> t

  (** Matching. *)
  module MatchF : Match.S with type t = conc_form

  (** Smart constructors and destructors for hypotheses. *)
  module Hyp : Term.SmartFO with type form = hyp_form

  (** Smart constructors and destructors for conclusions. *)
  module Conc : Term.SmartFO with type form = conc_form

end
