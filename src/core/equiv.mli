(** Equivalence formulas.  *)

open Utils
open Ppenv

module SE = SystemExpr
  
(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

(*------------------------------------------------------------------*)
type equiv = {terms : Term.term list; bound : Term.term option}

val pp_equiv : equiv formatter

val  pp_equiv_numbered : equiv formatter
val _pp_equiv_numbered : equiv formatter_p

(*------------------------------------------------------------------*)
val subst_equiv : Term.subst -> equiv -> equiv

(** Free variables of an [equiv]. *)
val fv_equiv : equiv -> Vars.Sv.t

(*------------------------------------------------------------------*)
(** {2 Formula with potential upper bound} *)
type bform = {formula : Term.term; bound : Term.term option}

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

  | Reach of bform
  (** Reach(φ) corresponds to [[φ]_{P1} ∧ [φ]_(P2) ∧ …]
      where the systems [Pi] are given by the [set] component of 
      the system context. *)

  | Pred of pred_app
  (** Fully applied predicate. Interpretation does not depend on the 
      system context, as all system arguments are explicit. *)

val pp_atom : atom formatter

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

val pp     : form formatter
val pp_dbg : form formatter

(** Full pretty printer.
    The [context] arguments allows to avoir printing some system expressions
    which are equal [context.set] or [context.pair]. *)
val _pp : ?context:SE.context -> form formatter_p

val _pp_conclusion : ?context:SE.context -> form formatter_p

(*------------------------------------------------------------------*)
val mk_quant_tagged : ?simpl:bool -> quant -> Vars.tagged_vars -> form -> form

val mk_reach_atom : ?e:Term.term -> Term.term -> form
val mk_equiv_atom : ?e:Term.term -> Term.term list -> form

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

val pp_any_form     : any_form formatter
val pp_any_form_dbg : any_form formatter
val _pp_any_form    : any_form formatter_p

val is_local  : any_form -> bool
val is_global : any_form -> bool

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

  val pp     :                        t formatter
  val pp_dbg :                        t formatter
  val _pp    : ?context:SE.context -> t formatter_p

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

  val pp     : 'a f_kind -> 'a formatter
  val pp_dbg : 'a f_kind -> 'a formatter

  val project : 'a f_kind -> Term.proj list -> 'a -> 'a
end

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors} *)
module Smart : SmartFO.S with type form = global_form

val destr_reach : form -> bform option
val destr_equiv : form -> equiv option
  
val is_equiv : form -> bool
val is_reach : form -> bool


(*------------------------------------------------------------------*)
(** {2 Generalized statements} *)

type any_statement = GlobalS of form | LocalS of bform

val pp_any_statement : any_statement formatter_p

val is_local_statement : any_statement -> bool

val any_statement_to_reach : any_statement -> bform
val any_statement_to_equiv : any_statement -> form

(*------------------------------------------------------------------*)
type _ s_kind =
  | Local_s  : bform         s_kind
  | Global_s : form          s_kind
  | Any_s    : any_statement s_kind

val s_kind_equal : 'a s_kind -> 'b s_kind -> bool

module Any_statement : sig
  type t = any_statement

  val pp     :                         t formatter
  val pp_dbg :                         t formatter
  val _pp    :  ?context:SE.context -> t formatter_p

  val equal : t -> t -> bool

  val subst  : Term.subst  -> t -> t
  val tsubst : Type.tsubst -> t -> t

  val fv    : t -> Vars.Sv.t
  val ty_fv : t -> Type.Fv.t

  val project : Term.proj list -> t -> t

  (** Convert any formula kind to [any_form]. *)
  val convert_from : 'a s_kind -> 'a -> t

  (** Convert [any_form] to any formula kind.
      Issue a soft failure (with the provided location, if any)
      when the input formula is not of the right kind. *)
  val convert_to : ?loc:Location.t -> 'a s_kind -> t -> 'a
end

(** Conversions between formula kinds and generic functionalities
    over all formula kinds. *)
module Babel_statement : sig
  val convert : ?loc:Location.t -> src:'a s_kind -> dst:'b s_kind -> 'a -> 'b

  val subst  : 'a s_kind -> Term.subst  -> 'a -> 'a
  val tsubst : 'a s_kind -> Type.tsubst -> 'a -> 'a

  val subst_projs :
    'a s_kind -> [`Equiv | `Reach] -> (Term.proj * Term.proj) list -> 'a -> 'a

  val fv     : 'a s_kind -> 'a -> Vars.Sv.t

  val get_terms : 'a s_kind -> 'a -> Term.term list

  val _pp    : 'a s_kind -> 'a formatter_p
  val pp     : 'a s_kind -> 'a formatter
  val pp_dbg : 'a s_kind -> 'a formatter

  val project : 'a s_kind -> Term.proj list -> 'a -> 'a
end
