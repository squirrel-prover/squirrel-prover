module L = Location

module TS = LowTraceSequent

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** As much as possible, hypotheses should be manipulated through the [Hyps] 
    module below, not the [H] module. 
    Ideally, this should not exported. *)
module H : Hyps.S with type hyp = Equiv.form
type hyps = H.hyps

(*------------------------------------------------------------------*)
include LowSequent.S with type form = Equiv.form

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent} *)

(** Initialize a sequent for the diff-equivalence of the given system.  
    Remark that if the projection of the system is not None, the goal will 
    be trivial. *)
val init : 
  SystemExpr.system_expr -> Symbols.table -> Vars.env -> hyps -> Equiv.form -> t

val pp_init : Format.formatter -> t -> unit

(*------------------------------------------------------------------*)
(** {2 Accessors and utils} *)

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
val trace_seq_of_equiv_seq : ?goal:Term.message -> t -> TS.t

val trace_seq_of_reach : Term.message -> t -> TS.t

val query_happens : precise:bool -> t -> Term.timestamp -> bool

val reach_to_form :             Term.message -> form
val form_to_reach : ?loc:L.t -> form -> Term.message
