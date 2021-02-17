module Hyps : Hyps.S with type hyp = Equiv.form

type hyps = Hyps.hyps

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent} *)

type t
type sequent = t

(** Initialize a sequent for the diff-equivalence of the given system.  
    Remark that if the projection of the system is not None, the goal will 
    be trivial. *)
val init : 
  SystemExpr.system_expr -> Symbols.table -> Vars.env -> hyps -> Equiv.form -> t

val pp : Format.formatter -> t -> unit

val pp_init : Format.formatter -> t -> unit

(** [apply_subst subst s] returns the sequent [s] where the substitution has
   been applied to its conclusion and hypotheses. *)
val subst : Term.subst -> t -> t

(*------------------------------------------------------------------*)
(** {2 Accessors and utils} *)

val env : t -> Vars.env
val set_env : Vars.env -> t -> t

val system : t -> SystemExpr.system_expr
val table  : t -> Symbols.table

val set_table  : t -> Symbols.table -> t

(** Get the list of biterms describing the two frames. *)
val goal : t -> Equiv.form

(** Return a new equivalence judgment with the given biframe. *)
val set_goal : t -> Equiv.form -> t

val set_equiv_goal : t -> Equiv.equiv -> t

(** Get the list of biterms describing the hypothesis frames. *)
val hyps : t -> hyps

(** Return a new equivalence judgment with the given hypothesis biframe. *)
val set_hyps : t -> hyps -> t

(** Get one of the projections of the biframe,
  * as a list of terms where diff operators have been fully
  * eliminated. *)
val get_frame : Term.projection -> t -> Equiv.equiv option
