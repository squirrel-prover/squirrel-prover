(* open Utils *)

(*------------------------------------------------------------------*)
module L = Location

module SE = SystemExpr

module TraceHyps = Hyps.TraceHyps
module EquivHyps = Hyps.EquivHyps

(*------------------------------------------------------------------*)
module type S = sig

  type t
  type sequent = t
  type sequents = sequent list

  val pp     :             Format.formatter -> t -> unit
  val _pp    : dbg:bool -> Format.formatter -> t -> unit
  val pp_dbg :             Format.formatter -> t -> unit

  (*------------------------------------------------------------------*)
  type hyp_form

  type conc_form

  val hyp_kind : hyp_form Equiv.f_kind
  val conc_kind : conc_form Equiv.f_kind

  (*------------------------------------------------------------------*)
  (** default variable information of the sequent *)
  val var_info : Vars.Tag.t

  (*------------------------------------------------------------------*)
  module Hyps : Hyps.S1 with type hyp = hyp_form and type hyps := t

  (** {2 Access to sequent components} *)

  val env : t -> Env.t
  val set_env : Env.t -> t -> t

  val vars : t -> Vars.env
  val set_vars : Vars.env -> t -> t

  val conclusion : t -> conc_form
  val set_conclusion : conc_form -> t -> t

  val system : t -> SystemExpr.context

  val set_conclusion_in_context :
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

  val mk_trace_cntxt : ?se:SE.fset -> t -> Constr.trace_cntxt

  val get_trace_hyps : t -> TraceHyps.hyps

  val get_models : t -> Constr.models

  (*------------------------------------------------------------------*) 
  (** {2 Substitution} *)

  val subst  : Term.subst  -> t -> t
  val tsubst : Type.tsubst -> t -> t

  val rename : Vars.var -> Vars.var -> t -> t

  (*------------------------------------------------------------------*) 
  (** {2 Free variables} *)

  val fv : t -> Vars.Sv.t

  (*------------------------------------------------------------------*) 
  (** {2 Misc} *)

  module Hyp : SmartFO.S with type form = hyp_form

  module Conc : SmartFO.S with type form = conc_form
end
