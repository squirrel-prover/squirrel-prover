(** {1 General sequent data-type}

    Definition of a general sequent data-type,
    which covers both local and global sequents
    (and thus equivalence sequents).

    A sequent is made of:
    - a set of (labelled) hypotheses;
    - a conclusion formula;
    - an environment containing the sequent's free variables.

    The signature defined here does not include functionalities
    relying on the list of the already proved goals:
    TODO this used to avoid a circular dependency, which is now
    fixed, and we may be able to simplify the architecture now. *)

open Utils
open Ppenv
    
module TraceHyps = Hyps.TraceHyps
module SE = SystemExpr

(** {2 Module type for sequents} *)
module type S = sig

  type t
  type sequent = t
  type sequents = sequent list

  (** Type of formulas used for sequent hypotheses. *)
  type hyp_form

  (** Type of formulas used for sequent conclusions. *)
  type conc_form


  val hyp_kind : hyp_form Equiv.f_kind
  val conc_kind : conc_form Equiv.f_kind

  (** Default variable information of the sequent. *)
  val var_info : Vars.Tag.t

  (*------------------------------------------------------------------*)
  (** {2 Pretty-printing} *)

  val pp     : t formatter
  val pp_dbg : t formatter
  val _pp    : t formatter_p

  (*------------------------------------------------------------------*)
  module Hyps : Hyps.S1 with type hyp = hyp_form and type hyps := t

  (** {2 Access to sequent components} *)

  val env : t -> Env.t
  val set_env : Env.t -> t -> t

  (** Return the variable environment of the sequent. This includes
      declared (free) variables, as well as defined variables (which
      also appear in the proof-context [hyps]). *)
  val vars : t -> Vars.env
  val set_vars : Vars.env -> t -> t

  val conclusion : t -> conc_form
  val set_conclusion : conc_form -> t -> t

  val bound : t -> Term.term option
  val set_bound : Term.term option -> t -> t

  val system : t -> SE.context

  val params : t -> Params.t

  val table : t -> Symbols.table
  val set_table : Symbols.table -> t -> t

  val ty_vars : t -> Type.tvars

  (*------------------------------------------------------------------*)
  (** {2 Context change} *)

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
  val set_conclusion_in_context :
    ?update_local:(Term.term -> Term.term option) ->
    ?bound :Term.term ->
    SE.context -> conc_form -> t -> t

  (*------------------------------------------------------------------*)
  (** {2 Manipulation of bi-frame elements}

      These functionalities only make sense for equivalence sequents. *)

  val mem_felem    : int -> t -> bool
  val change_felem : ?loc:Location.t -> int -> Term.term list -> t -> t
  val get_felem    : ?loc:Location.t -> int -> t -> Term.term

  (*------------------------------------------------------------------*)
  (** {2 Automated reasoning} *)

  val query_happens : precise:bool -> t -> Term.term -> bool

  (** Returns the proof-context of a sequent.
      Option projections to restrict the systems considered. *)
  val proof_context : ?in_system:SE.context -> t -> ProofContext.t

  (** Return a set of hypotheses that are a consequence of the
      hypotheses of the sequent, and are taken in the system context
      [in_system].

      [in_system] defaults to [s]'s system. *)
  val get_trace_hyps : ?in_system:SE.context -> t -> TraceHyps.hyps

  (** [get_models s] returns a set of minimal models corresponding to the
      trace atoms in the sequent [s].
      Definitions inside [s] are kept if they follow the optional [system].
      See module {!Constr}.
      @raise Tactics.Tactic_hard_failure
         with parameter {!Tactics.TacTimeout} in case of timeout. *)
  val get_models :
    SE.arbitrary option ->
    t -> Constr.models

  (*------------------------------------------------------------------*)
  (** {2 Substitution} *)

  (** [subst subst s] returns the sequent [s] where the substitution has
      been applied to all hypotheses and the conclusion.
      It removes trivial equalities (e.g x=x). *)
  val subst : Term.subst -> t -> t

  (** Same but for a type substitution. *)
  val gsubst : t Subst.substitution

  (** [rename u v s] returns the sequent [s] where
      free variable u is replaced with v *)
  val rename : Vars.var -> Vars.var -> t -> t

  (*------------------------------------------------------------------*)
  (** {2 Free variables} *)

  val fv : t -> Vars.Sv.t

  (*------------------------------------------------------------------*)
  (** {2 Smart constructors and destructors} *)

  (** Smart constructors and destructors for hypotheses. *)
  module Hyp : SmartFO.S with type form = hyp_form

  (** Smart constructors and destructors for conclusions. *)
  module Conc : SmartFO.S with type form = conc_form

end

