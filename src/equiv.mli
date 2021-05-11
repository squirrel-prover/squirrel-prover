(** Equivalence formulas.  *)

(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

val pi_term : Term.projection -> 'a Term.term -> 'a Term.term

(*------------------------------------------------------------------*)
type equiv = Term.message list

val pp_equiv : Format.formatter -> equiv -> unit
val pp_equiv_numbered : Format.formatter -> equiv -> unit

val subst_equiv : Term.subst -> equiv -> equiv

(** Free variables of an [equiv]. *)
val fv_equiv : equiv -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** {2 Equivalence atoms} *)

type atom = 
  | Equiv of equiv
  (** Equiv u corresponds to (u)^left ~ (u)^right *)

  | Reach of Term.message
  (** Reach(φ) corresponds to (φ)^left ~ ⊤ ∧ (φ)^right ~ ⊤ *)

val pp_atom : Format.formatter -> atom -> unit

val subst_atom : Term.subst -> atom -> atom

(** Free variables *)
val fv_atom : atom -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)
(** We only support a small fragment for now *)

type form = 
  | ForAll of Vars.evar list * form
  | Atom   of atom
  | Impl   of (form * form)

val pp : Format.formatter -> form -> unit

val mk_forall : Vars.evar list -> form -> form

val mk_reach_atom : Term.message -> form

val subst : Term.subst -> form -> form

(** Free variables *)
val fv : form -> Vars.Sv.t
