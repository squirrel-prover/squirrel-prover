module L = Location

type lsymb = Theory.lsymb

(** As much as possible, hypotheses should be manipulated through the [Hyps] 
    module below, not the [H] module. 
    Ideally, this should not exported. *)
module H : Hyps.S with type hyp = Equiv.form
type hyps = H.hyps

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent} *)

type t
type sequent = t

type sequents = sequent list


type form = Equiv.form

(** Initialize a sequent for the diff-equivalence of the given system.  
    Remark that if the projection of the system is not None, the goal will 
    be trivial. *)
val init : 
  SystemExpr.system_expr -> Symbols.table -> Vars.env -> hyps -> Equiv.form -> t

val pp : Format.formatter -> t -> unit

val pp_init : Format.formatter -> t -> unit

(** [apply_subst subst s] returns the sequent [s] where the substitution has
   been applied to its conclusion and hypotheses. *)
val subst     : Term.subst -> t -> t

val subst_hyp : Term.subst -> form -> form

(*------------------------------------------------------------------*)
(** {2 Hypotheses functions} *)

(** Built on top of [Hyps.H].*)
module Hyps : Hyps.HypsSeq with type hyp = Equiv.form and type sequent = t

(*------------------------------------------------------------------*)
(** {2 Accessors and utils} *)

val env : t -> Vars.env
val set_env : Vars.env -> t -> t

val system : t -> SystemExpr.system_expr
val set_system : SystemExpr.system_expr -> t -> t

val table  : t -> Symbols.table

val set_table  : Symbols.table -> t -> t

(** Get the list of biterms describing the two frames. *)
val goal : t -> Equiv.form

val ty_vars : t -> Type.tvars

(** Return a new equivalence judgment with the given biframe. *)
val set_goal : Equiv.form -> t -> t

val set_equiv_goal : Equiv.equiv -> t -> t

val set_ty_vars : Type.tvars -> t -> t

(** Get the list of biterms describing the hypothesis frames. *)
val hyps : t -> hyps

(** Return a new equivalence judgment with the given hypothesis biframe. *)
val set_hyps : hyps -> t -> t

(** Get one of the projections of the biframe,
  * as a list of terms where diff operators have been fully
  * eliminated. *)
val get_frame : Term.projection -> t -> Equiv.equiv option

val goal_is_equiv : t -> bool

val goal_as_equiv : t -> Equiv.equiv

val set_reach_goal : Term.message -> t -> t

(** Build a trace sequent from an equivalent sequent when its conclusion is 
    a [Reach _]. *)
val trace_seq_of_equiv_seq : ?goal:Term.message -> t -> TraceSequent.t

val trace_seq_of_reach : Term.message -> t -> TraceSequent.t

val get_terms : form -> Term.message list
val get_models : t -> Constr.models

val mk_trace_cntxt : t -> Constr.trace_cntxt

val query_happens : precise:bool -> t -> Term.timestamp -> bool

val reach_to_form :             Term.message -> form
val form_to_reach : ?loc:L.t -> form -> Term.message

(*------------------------------------------------------------------*)
val mem_felem    : int -> t -> bool
val change_felem : int -> Term.message list -> t -> t
val get_felem    : int -> t -> Term.message

(*------------------------------------------------------------------*)
(** {2 Matching} *)
module Match : Term.MatchS with type t = form

(*------------------------------------------------------------------*)
module Smart : Term.SmartFO with type form = form
