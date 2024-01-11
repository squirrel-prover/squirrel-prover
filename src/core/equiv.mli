(** Equivalence formulas.  *)

module SE = SystemExpr
  
(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

(*------------------------------------------------------------------*)
type equiv = Term.term list

val pp_equiv : Format.formatter -> equiv -> unit

val  pp_equiv_numbered :             Format.formatter -> equiv -> unit
val _pp_equiv_numbered : dbg:bool -> Format.formatter -> equiv -> unit

(*------------------------------------------------------------------*)
val subst_equiv : Term.subst -> equiv -> equiv

(** Free variables of an [equiv]. *)
val fv_equiv : equiv -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** {2 Equivalence atoms} *)

type pred_app = {
  psymb      : Symbols.predicate;        (** Predicate symbol *)
  ty_args    : Type.ty list;             (** Type arguments *)
  se_args    : SE.t list;                (** System expression arguments *)  
  multi_args : (SE.t * Term.terms) list;
  (** Multi-term args with their system expression. *)
  simpl_args : Term.terms;               (** Simple arguments *)
}

(** Global formula atom, to be interpreted relatively to a 
    system context (e.g. specified by the sequent). *)
type atom =
  | Equiv of equiv
  (** Equiv u corresponds to (u)^left ~ (u)^right
      where the systems [left, right] are given by the [pair] component 
      of the system context. *)

  | Reach of Term.term
  (** Reach(φ) corresponds to [[φ]_{P1} ∧ [φ]_(P2) ∧ …]
      where the systems [Pi] are given by the [set] component of 
      the system context. *)

  | Pred of pred_app
  (** Fully applied predicate. Interpretation does not depend on the 
      system context, as all system arguments are explicit. *)

val pp_atom : Format.formatter -> atom -> unit

val subst_atom : Term.subst -> atom -> atom

(** Free variables *)
val fv_atom : atom -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)
(** We only support a small fragment for now *)

type quant = ForAll | Exists

type form = 
  | Quant of quant * Vars.tagged_vars * form
  | Let   of Vars.var * Term.term * form
  (** The system context of the [term] is [pair] *)
  | Atom  of atom
  | Impl  of form * form
  | And   of form * form
  | Or    of form * form

val pp     : Format.formatter -> form -> unit
val pp_dbg : Format.formatter -> form -> unit

(** Full pretty printer.
    The [context] arguments allows to avoir printing some system expressions
    which are equal [context.set] or [context.pair]. *)
val _pp : dbg:bool -> ?context:SE.context -> Format.formatter -> form -> unit

(*------------------------------------------------------------------*)
val mk_quant_tagged : ?simpl:bool -> quant -> Vars.tagged_vars -> form -> form

val mk_reach_atom : Term.term -> form
val mk_equiv_atom : Term.term list -> form

(*------------------------------------------------------------------*)
(** Does not recurse. *)
val tmap       : (form -> form) -> form -> form 
val titer      : (form -> unit) -> form -> unit
val tforall    : (form -> bool) -> form -> bool 
val texists    : (form -> bool) -> form -> bool 
val tfold      : (form -> 'a -> 'a) -> form -> 'a -> 'a
val tmap_fold  : ('b -> form -> 'b * form) -> 'b -> form -> 'b * form 

(*------------------------------------------------------------------*)
(** Get (some) terms appearing in a formula.
  * For instance, terms occurring under binders may not be included. *)
val get_terms : form -> Term.term list

(*------------------------------------------------------------------*)
(** Project the reachability formulas in a global formula. *)
val project : Term.proj list -> form -> form 

(*------------------------------------------------------------------*)
(** Checks if a formula is independent of the system context,
    i.e. does not contain reachability or equivalence atoms. *)
val is_system_context_indep : form -> bool

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

val subst       : Term.subst  -> form -> form
val tsubst      : Type.tsubst -> form -> form
val se_subst    : SE.subst    -> form -> form

(** Substitute projections in [Equiv] or [Reach] atoms. *)
val subst_projs :
  [`Equiv | `Reach] -> (Term.proj * Term.proj) list -> form -> form

(** Free variables *)
val fv : form -> Vars.Sv.t

(** Free type variables *)
val ty_fv  : form      -> Type.Fv.t
val ty_fvs : form list -> Type.Fv.t

(*------------------------------------------------------------------*)
(** {2 Generalized formuals} *)

(** A local meta-formula is a boolean term. *)
type local_form = Term.term

type global_form = form

type any_form = Global of form | Local of Term.term

val pp_any_form : Format.formatter -> any_form -> unit

val is_local : any_form -> bool

val any_to_reach : any_form -> Term.term 
val any_to_equiv : any_form -> form 

(*------------------------------------------------------------------*)
type _ f_kind =
  | Local_t  : local_form  f_kind
  | Global_t : global_form f_kind
  | Any_t    : any_form    f_kind

val kind_equal : 'a f_kind -> 'b f_kind -> bool
  
module Any : sig
  type t = any_form

  val pp     : Format.formatter -> t -> unit
  val pp_dbg : Format.formatter -> t -> unit
  val _pp    : dbg:bool -> ?context:SE.context -> Format.formatter -> t -> unit

  val equal : t -> t -> bool

  val subst  : Term.subst  -> t -> t
  val tsubst : Type.tsubst -> t -> t

  val fv    : t -> Vars.Sv.t
  val ty_fv : t -> Type.Fv.t

  val project : Term.proj list -> t -> t
    
  (** Convert any formula kind to [any_form]. *)
  val convert_from : 'a f_kind -> 'a -> any_form

  (** Convert [any_form] to any formula kind.
    * Issue a soft failure (with the provided location, if any)
    * when the input formula is not of the right kind. *)
  val convert_to : ?loc:Location.t -> 'a f_kind -> any_form -> 'a

  module Smart : SmartFO.S with type form = any_form
end

(** Conversions between formula kinds and generic functionalities
    over all formula kinds. *)
module Babel : sig
  val convert : ?loc:Location.t -> src:'a f_kind -> dst:'b f_kind -> 'a -> 'b

  val subst  : 'a f_kind -> Term.subst  -> 'a -> 'a
  val tsubst : 'a f_kind -> Type.tsubst -> 'a -> 'a

  val subst_projs : 
    'a f_kind -> [`Equiv | `Reach] -> (Term.proj * Term.proj) list -> 'a -> 'a

  val fv     : 'a f_kind -> 'a -> Vars.Sv.t

  val get_terms : 'a f_kind -> 'a -> Term.term list

  val pp     : 'a f_kind -> Format.formatter -> 'a -> unit
  val pp_dbg : 'a f_kind -> Format.formatter -> 'a -> unit

  val project : 'a f_kind -> Term.proj list -> 'a -> 'a
end

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructots} *)
module Smart : SmartFO.S with type form = global_form

val destr_reach : form -> Term.term option
val destr_equiv : form -> equiv option
  
val is_equiv : form -> bool
val is_reach : form -> bool

