(** Equivalence formulas.  *)

(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

type elem =
  | Formula of Term.formula
  | Message of Term.message

val pp_elem : Format.formatter -> elem -> unit

val pi_term : Term.projection -> 'a Term.term -> 'a Term.term
val pi_elem : Term.projection -> elem -> elem

(** Free variables of an [elem]. *)
val fv_elem : elem -> Vars.Sv.t

(*------------------------------------------------------------------*)
type equiv = elem list

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

  | Reach of Term.formula
  (** Reach(φ) corresponds to (φ)^left ~ ⊤ ∧ (φ)^right ~ ⊤ *)

val pp_atom : Format.formatter -> atom -> unit

val subst_atom : Term.subst -> atom -> atom

(** Free variables of an [atom]. *)
val fv_atom : atom -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)
(** We only support a small fragment for now *)

type form = 
  | Atom of atom
  | Impl of (form * form)

val pp_form : Format.formatter -> form -> unit

val subst_form : Term.subst -> form -> form

(** Free variables of an [atom]. *)
val fv_form : form -> Vars.Sv.t
