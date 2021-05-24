type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Module type for sequents} *)

module type S = sig
  type t
  type sequent = t
  type sequents = sequent list
    
  val pp : Format.formatter -> t -> unit

  (** type of hypotheses and goals *)
  type form

  val pp_form : Format.formatter -> form -> unit

  module Hyps : Hyps.HypsSeq with type hyp = form and type sequent = t

  val reach_to_form : Term.message -> form

  (** the environment of the sequent. *)
  val env : t -> Vars.env
  val set_env : Vars.env -> t -> t

  (** the goal of the sequent. *)
  val goal : t -> form
  val set_goal : form -> t -> t
  val set_reach_goal : Term.message -> t -> t

  (** the system of the sequent *)
  val system : t -> SystemExpr.system_expr
  val set_system : SystemExpr.system_expr -> t -> t

  (** the symbol table of the sequent. *)
  val table : t -> Symbols.table
  val set_table  : Symbols.table -> t -> t

  val ty_vars : t -> Type.tvars 

  val mem_felem    : int -> t -> bool
  val change_felem : int -> Term.message list -> t -> t
  val get_felem    : int -> t -> Term.message

  val query_happens : precise:bool -> t -> Term.timestamp -> bool

  val mk_trace_cntxt : t -> Constr.trace_cntxt

  val get_trace_literals : t -> Term.trace_literal list

  val get_hint_db : t -> Hint.hint_db

  val get_models : t -> Constr.models

  val subst     : Term.subst ->   t ->   t
  val subst_hyp : Term.subst -> form -> form

  (** get (some) terms appearing in an hypothesis.
      In an equiv formula, does not return terms under (equiv) binders. *)
  val get_terms : form -> Term.message list

  val map : (form -> form) -> t -> t

  (*------------------------------------------------------------------*)
  (** {3 Matching} *)
  module Match : Term.MatchS with type t = form

  (*------------------------------------------------------------------*)
  (** {3 Smart constructors and destructots} *)
  module Smart : Term.SmartFO with type form = form  
end
