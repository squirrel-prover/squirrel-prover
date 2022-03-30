(** Terms and formulas for the meta-logic.

    This module describes the syntax of the logic. It does not
    provide low-level representations, normal forms, etc. that
    are to be used in automated reasoning, nor does it provide
    representations necessary for the front-end involving
    processes, axioms, etc. *)

(*------------------------------------------------------------------*)
(** {2 Symbols}

    We have function, name and macro symbols. Each symbol
    can then be indexed. *)

(** Ocaml type of a typed index symbol.
    Invariant: [s_typ] do not contain tvar or univars. *)
type 'a isymb = private {
  s_symb    : 'a;
  s_indices : Vars.var list;
  s_typ     : Type.ty;
}

val mk_isymb : 'a -> Type.ty -> Vars.vars -> 'a isymb

(** Names represent random values of length the security parameter. *)

type name = Symbols.name 
type nsymb = name isymb

(** Function symbols, may represent primitives or abstract functions. *)

type fname = Symbols.fname 
type fsymb = fname * Vars.var list

(** Macros are used to represent inputs, outputs, contents of state
    variables, and let definitions: everything that is expanded when
    translating the meta-logic to the base logic. *)

type mname = Symbols.macro 
type msymb = mname isymb

type state = msymb

(*------------------------------------------------------------------*)
(** {3 Pretty printing} *)

val pp_name  : Format.formatter -> name -> unit
val pp_nsymb : Format.formatter -> nsymb -> unit

val pp_fname : Format.formatter -> fname -> unit
val pp_fsymb : Format.formatter -> fsymb -> unit

val pp_mname :  Format.formatter -> mname -> unit
val pp_msymb :  Format.formatter -> msymb -> unit

(*------------------------------------------------------------------*)
(** {2 Terms}

  In this module {!term} describe both terms and formulas of the meta-logic. *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

val pp_ord : Format.formatter -> ord -> unit

type term = private
  | Fun   of fsymb * Type.ftype * term list
  | Name  of nsymb
  | Macro of msymb * term list * term

  | Seq    of Vars.var list * term
  | Action of Symbols.action * Vars.var list 

  | Var of Vars.var

  | Diff of term * term

  | Find of Vars.var list * term * term * term 

  | ForAll of Vars.var list * term 
  | Exists of Vars.var list * term 

type t = term

type terms = term list

val hash : term -> int

(*------------------------------------------------------------------*)
(** Does not recurse. *)
val tmap       : (term -> term) -> term -> term
val titer      : (term -> unit) -> term -> unit
val tfold      : (term -> 'a -> 'a) -> term -> 'a -> 'a
val tmap_fold  : ('b -> term -> 'b * term) -> 'b -> term -> 'b * term

(*------------------------------------------------------------------*)
(** {2 Literals} *)

type ('a,'b) _atom = 'a * 'b * 'b

type xatom = [
  | `Comp    of (ord,term) _atom
  | `Happens of term
]

type literal = [`Neg | `Pos] * xatom

type literals = literal list

(** Type of compared elements. *)
val ty_xatom : xatom -> Type.ty

(** Type of compared elements. *)
val ty_lit  : literal -> Type.ty

val pp_literal  : Format.formatter -> literal  -> unit
val pp_literals : Format.formatter -> literals -> unit

val neg_lit : literal -> literal

val disjunction_to_literals : term -> literal list option

val form_to_xatom   : term ->   xatom option
val form_to_literal : term -> literal option

(** Given a formula, return a list of literals which is either
    entailed by the formula, or equivalent to the formula. *)
val form_to_literals :
  term -> [`Entails of literal list | `Equiv of literal list]

val xatom_to_form : xatom   -> term
val lit_to_form   : literal -> term

(*------------------------------------------------------------------*)
(** {2 Higher-order terms} *)

type hterm = Lambda of Vars.vars * term

val pp_hterm : Format.formatter -> hterm -> unit

(*------------------------------------------------------------------*)
(** {2 Pretty-printer and cast} *)

(** Additional printing information *)
type pp_info

val default_pp_info : pp_info

val pp : Format.formatter -> term -> unit

val pp_with_info : pp_info -> Format.formatter -> term -> unit

(*------------------------------------------------------------------*)
val ty  : ?ty_env:Type.Infer.env -> term -> Type.ty

(*------------------------------------------------------------------*)
(** [get_vars t] returns the free variables of [t].
  * The returned list is guaranteed to have no duplicate elements. *)
val get_vars : term -> Vars.var list

(** [fv t] returns the free variables of [t]. *)
val fv : term -> Vars.Sv.t

val f_triv : term -> bool

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

(** Substitutions for all purpose, applicable to terms and timestamps.
    {b TODO} unusually, we map terms to terms and not just variables to terms;
    this is used somewhere... but I forgot where. *)
type esubst = ESubst of term * term 

type subst = esubst list

val pp_subst : Format.formatter -> subst -> unit

val is_var_subst : subst -> bool

val subst_support : subst -> Vars.Sv.t

val subst_binding : Vars.var -> subst -> Vars.var * subst

(** term substitution *)
val subst : subst -> term -> term

(** substitute type variables *)
val tsubst : Type.tsubst -> term -> term

val tsubst_ht : Type.tsubst -> hterm -> hterm

(** [subst_var s v] returns [v'] if substitution [s] maps [v] to [Var v'],
    and [v] if the variable is not in the domain of the substitution.
    @raise Substitution_error if [v] is mapped to a non-variable term in [s]. *)
val subst_var  : subst -> Vars.var -> Vars.var

(** Substitute indices in an indexed symbols. *)
val subst_isymb : subst -> 'a isymb -> 'a isymb

(** [subst_macros_ts table l ts t] replaces [ts] by [pred(ts)] in the term [t]
  * if [ts] is applied to a state macro whose name is NOT in [l]. *)
val subst_macros_ts : Symbols.table -> string list -> term -> term -> term

(*------------------------------------------------------------------*)
type refresh_arg = [`Global | `InEnv of Vars.env ref ]

val refresh_vars  : refresh_arg -> Vars.vars -> Vars.vars * esubst list

val refresh_vars_env :
  Vars.env -> Vars.var list -> Vars.env * Vars.var list * esubst list

(*------------------------------------------------------------------*)
val apply_ht : hterm -> term list -> hterm

(*------------------------------------------------------------------*)
(** {2 Builtins function symbols} *)

val empty : term
val init : term

val in_macro    : msymb
val out_macro   : msymb
val frame_macro : msymb
val cond_macro  : msymb
val exec_macro  : msymb

val f_happens : fsymb

val f_pred : fsymb

val f_true  : fsymb
val f_false : fsymb
val f_and   : fsymb
val f_impl  : fsymb
val f_or    : fsymb
val f_not   : fsymb
val f_ite   : fsymb

val f_eq  : fsymb
val f_neq : fsymb
val f_leq : fsymb
val f_lt  : fsymb
val f_geq : fsymb
val f_gt  : fsymb

val f_diff : fsymb

val f_succ : fsymb

val f_att : fsymb

val f_fail : fsymb

val f_xor  : fsymb
val f_zero : fsymb

val f_pair : fsymb
val f_fst  : fsymb
val f_snd  : fsymb

val f_of_bool : fsymb

val f_len    : fsymb
val f_zeroes : fsymb

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors} *)

(** Module type for smart constructors and destructors on first-order formulas,
    where the type is abstracted. Instantiated by both [Term] and [Equiv]. *)
module type SmartFO = sig
  type form

  (** {3 Constructors} *)
  val mk_true  : form
  val mk_false : form

  val mk_eq  : ?simpl:bool -> term -> term -> form
  val mk_leq : ?simpl:bool -> term -> term -> form
  val mk_geq : ?simpl:bool -> term -> term -> form
  val mk_lt  : ?simpl:bool -> term -> term -> form
  val mk_gt  : ?simpl:bool -> term -> term -> form

  val mk_not   : ?simpl:bool -> form              -> form
  val mk_and   : ?simpl:bool -> form      -> form -> form
  val mk_ands  : ?simpl:bool -> form list         -> form
  val mk_or    : ?simpl:bool -> form      -> form -> form
  val mk_ors   : ?simpl:bool -> form list         -> form
  val mk_impl  : ?simpl:bool -> form      -> form -> form
  val mk_impls : ?simpl:bool -> form list -> form -> form

  val mk_forall : ?simpl:bool -> Vars.vars -> form -> form
  val mk_exists : ?simpl:bool -> Vars.vars -> form -> form

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  val destr_forall  : form -> (Vars.var list * form) option
  val destr_forall1 : form -> (Vars.var      * form) option
  val destr_exists  : form -> (Vars.var list * form) option
  val destr_exists1 : form -> (Vars.var      * form) option

  (*------------------------------------------------------------------*)
  val destr_neq : form -> (term * term) option
  val destr_eq  : form -> (term * term) option
  val destr_leq : form -> (term * term) option
  val destr_lt  : form -> (term * term) option

  (*------------------------------------------------------------------*)
  val destr_false : form ->         unit  option
  val destr_true  : form ->         unit  option
  val destr_not   : form ->         form  option
  val destr_and   : form -> (form * form) option
  val destr_or    : form -> (form * form) option
  val destr_impl  : form -> (form * form) option

  (*------------------------------------------------------------------*)
  val is_false  : form -> bool
  val is_true   : form -> bool
  val is_not    : form -> bool
  val is_zero   : form -> bool
  val is_and    : form -> bool
  val is_or     : form -> bool
  val is_impl   : form -> bool
  val is_forall : form -> bool
  val is_exists : form -> bool

  (*------------------------------------------------------------------*)
  val is_neq : form -> bool
  val is_eq  : form -> bool
  val is_leq : form -> bool
  val is_lt  : form -> bool

  (*------------------------------------------------------------------*)
  (** left-associative *)
  val destr_ands  : int -> form -> form list option
  val destr_ors   : int -> form -> form list option
  val destr_impls : int -> form -> form list option

  (*------------------------------------------------------------------*)
  val decompose_forall : form -> Vars.var list * form
  val decompose_exists : form -> Vars.var list * form

  (*------------------------------------------------------------------*)
  val decompose_ands  : form -> form list
  val decompose_ors   : form -> form list
  val decompose_impls : form -> form list

  val decompose_impls_last : form -> form list * form
end

module Smart : SmartFO with type form = term

include module type of Smart

(*------------------------------------------------------------------*)
(** {3 Smart constructors: terms} *)

val mk_pred   : term -> term
val mk_var    : Vars.var -> term
val mk_action : Symbols.action -> Vars.var list -> term
val mk_name   : nsymb -> term
val mk_macro  : msymb -> term list -> term -> term
val mk_diff   : term -> term -> term

val mk_find : Vars.var list -> term -> term -> term -> term


(*------------------------------------------------------------------*)
val mk_fun0 : fsymb -> Type.ftype -> term list -> term

val mk_fun :
  Symbols.table ->
  fname ->
  Vars.var list ->
  term list ->
  term

val mk_zero    : term
val mk_fail    : term
val mk_len     : term -> term
val mk_zeroes  : term -> term
val mk_of_bool : term -> term
val mk_pair    : term -> term -> term

val mk_witness : Type.ty -> term

(*------------------------------------------------------------------*)
(** {3 Smart constructors: messages} *)

val mk_ite : ?simpl:bool -> term -> term -> term -> term

val mk_timestamp_leq : term -> term -> term

val mk_indices_neq :                Vars.var list -> Vars.var list -> term
val mk_indices_eq  : ?simpl:bool -> Vars.var list -> Vars.var list -> term

val mk_atom : ord -> term -> term -> term
val mk_happens : term -> term

val mk_seq0 : ?simpl:bool -> Vars.vars -> term -> term

(** Refresh variables *)
val mk_seq : Vars.env -> Vars.vars -> term -> term

(*------------------------------------------------------------------*)
(** {3 Destructors} *)

val is_binder : term -> bool

val is_macro  : term -> bool

val is_name : term -> bool

val destr_var : term -> Vars.var option

(*------------------------------------------------------------------*)
val destr_action : term -> (Symbols.action * Vars.var list) option

(*------------------------------------------------------------------*)
val destr_pair : term -> (term * term) option


(*------------------------------------------------------------------*)
(** {2 Simplification} *)

val not_simpl : term -> term

(** Check if a formula represents a deterministic (i.e. 
    non-probabilistic) computation. *)
val is_deterministic : term -> bool

(** Check if a formula only depends on the trace model. *)
val is_pure_timestamp : term -> bool

(*------------------------------------------------------------------*)
(** {2 Sets and Maps } *)

module St : Set.S with type elt = term
module Mt : Map.S with type key = term

(*------------------------------------------------------------------*)
(** {2 Convert from bi-terms to terms}

    {b TODO} Could we use a strong typing of [term] to make a static
    distinction between biterms (general terms) and terms (terms
    without diff operators)? *)

type projection = PLeft | PRight | PNone

val pp_projection : Format.formatter -> projection -> unit


(** Evaluate all diff operators wrt a projection.
    If the projection is [None], the input term is returned unchanged.
    Otherwise all diff operators are evaluated to the given
    side and the returned term does not feature diff operators.
    If the bi-term contains macros, and come from a bi-system, its
    projection is only correctly interpreted if it is used inside
    the projected system.
    *)
val pi_term :  projection:projection -> term -> term

(** Evaluate topmost diff operators
  * for a given projection of a biterm.
  * For example [head_pi_term Left (diff(f(diff(a,b)),c))]
  * would be [f(diff(a,b))].
  * Macros are returned without suspended projections over them. *)
val head_pi_term : projection -> term -> term

(** Push topmost diff-operators just enough to expose the common
  * topmost constructor of the two projections of a biterm.
  *
  * Macros with different timestamps do not count as a common
  * constructor: [head_normal_biterm (Diff(Macro(m,l,ts),Macro(m,l,ts')))]
  * will be [Diff(Macro(m,l,ts),Macro(m,l,ts'))] and not
  * [Macro(m,l,Diff(ts,ts'))].
  *
  * If the returned biterm starts with a diff, then its immediate
  * subterms have topmost different constructors, and they do not
  * start with diffs themselves. *)
val head_normal_biterm : term -> term

val make_bi_term : term -> term -> term

val simple_bi_term : term -> term

(*------------------------------------------------------------------*)
(** {2 Matching information for error messages} *)

type match_info =
  | MR_ok                      (* term matches *)
  | MR_check_st of term list   (* need to look at subterms *)
  | MR_failed                  (* term does not match *)

type match_infos = match_info Mt.t

val pp_match_info : Format.formatter -> match_info -> unit

val pp_match_infos : Format.formatter -> match_infos -> unit

val match_infos_to_pp_info : match_infos -> pp_info
