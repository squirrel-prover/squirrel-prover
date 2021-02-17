type elem =
  | Formula of Term.formula
  | Message of Term.message

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)

type equiv = elem list

val pp_equiv : Format.formatter -> equiv -> unit
val subst_equiv : Term.subst -> equiv -> equiv


(*------------------------------------------------------------------*)
(** {2 Equivalence sequent hypotheses} *)

type hyp = 
  | Equiv of equiv
  (* Equiv u corresponds to (u)^left ~ (u)^right *)

  | Reach of Term.formula
  (* Reach(φ) corresponds to (φ)^left ~ ⊤ ∧ (φ)^right ~ ⊤ *)


type hyps = hyp list

val pp_hyp  : Format.formatter -> hyp  -> unit
val pp_hyps : Format.formatter -> hyps -> unit

val subst_hyp  : Term.subst -> hyp  -> hyp
val subst_hyps : Term.subst -> hyps -> hyps

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent} *)

type t
type sequent = t

(** Initialize a sequent for the diff-equivalence of the given system.  
    Remark that if the projection of the system is not None, the goal will 
    be trivial. *)
val init : 
  SystemExpr.system_expr -> Symbols.table -> Vars.env -> hyps -> equiv -> t

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
val goal : t -> equiv

(** Return a new equivalence judgment with the given biframe. *)
val set_goal : t -> equiv -> t

(** Get the list of biterms describing the hypothesis frames. *)
val hyps : t -> hyps

(** Return a new equivalence judgment with the given hypothesis biframe. *)
val set_hyps : t -> hyps -> t

(** Get one of the projections of the biframe,
  * as a list of terms where diff operators have been fully
  * eliminated. *)
val get_frame : Term.projection -> t -> equiv

(** Project a biterm of the frame to one side. *)
val pi_elem : Term.projection -> elem -> elem
