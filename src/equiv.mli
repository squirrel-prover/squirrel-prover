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

type quant = ForAll | Exists

type form = 
  | Quant of quant * Vars.evar list * form
  | Atom  of atom
  | Impl  of form * form
  | And   of form * form
  | Or    of form * form

val pp : Format.formatter -> form -> unit

val mk_quant  : quant -> Vars.evar list -> form -> form
val mk_forall :          Vars.evar list -> form -> form
val mk_exists :          Vars.evar list -> form -> form

val mk_reach_atom : Term.message -> form

(** Does not recurse. *)
val tmap       : (form -> form) -> form -> form 
val titer      : (form -> unit) -> form -> unit
val tfold      : (form -> 'a -> 'a) -> form -> 'a -> 'a
val tmap_fold  : ('b -> form -> 'b * form) -> 'b -> form -> 'b * form 

(** Get (some) terms appearing in a formula.
  * For instance, terms occurring under binders may not be included. *)
val get_terms : form -> Term.message list

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

val subst : Term.subst -> form -> form

val tsubst : Type.tsubst -> form -> form
  
(** Free variables *)
val fv : form -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** {2 Generalized formuals} *)

(** A local meta-formula is a boolean term. *)
type local_form = Term.message

type global_form = form

type gform = [`Equiv of form | `Reach of Term.message]
type any_form = gform

type _ f_kind =
  | Local_t : local_form f_kind
  | Global_t : global_form f_kind
  | Any_t : any_form f_kind

module Any : sig
  type t = any_form

  val pp : Format.formatter -> t -> unit
  val subst : Term.subst -> t -> t
  val fv : t -> Vars.Sv.t

  (** Convert any formula kind to [any_form]. *)
  val convert_from : 'a f_kind -> 'a -> any_form

  (** Convert [any_form] to any formula kind.
    * Issue a soft failure (with the provided location, if any)
    * when the input formula is not of the right kind. *)
  val convert_to : ?loc:Location.t -> 'a f_kind -> any_form -> 'a

  module Smart : Term.SmartFO with type form = any_form
end

(** Conversions between formula kinds and generic functionalities
  * over all formula kinds. *)
module Babel : sig
  type mapper = {
    call : 'a. 'a f_kind -> 'a -> 'a
  }
  val convert : ?loc:Location.t -> src:'a f_kind -> dst:'b f_kind -> 'a -> 'b
  val subst  : 'a f_kind -> Term.subst -> 'a -> 'a
  val tsubst : 'a f_kind -> Type.tsubst -> 'a -> 'a
  val fv     : 'a f_kind -> 'a -> Vars.Sv.t
  val get_terms : 'a f_kind -> 'a -> Term.message list
  val pp : 'a f_kind -> Format.formatter -> 'a -> unit
end

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructots} *)
module Smart : Term.SmartFO with type form = global_form
