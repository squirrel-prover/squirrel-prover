(** Terms and formulas for the meta-logic.

    This module describes the syntax of the logic. It does not
    provide low-level representations, normal forms, etc. that
    are to be used in automated reasoning, nor does it provide
    representations necessary for the front-end involving
    processes, axioms, etc. *)

open Utils

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** {2 Symbols}

    We have function, name and macro symbols.
    Each symbol can then be indexed.
    TODO document the more general treatment of function symbols. *)

(** A typed symbol.
    Invariant: [s_typ] do not contain tvar or univars. *)
type 'a isymb = private {
  s_symb    : 'a;
  s_typ     : Type.ty;
}

val mk_symb : 'a -> Type.ty -> 'a isymb

(** Names represent random values of length the security parameter. *)
type nsymb = Symbols.name isymb

(** Macros are used to represent inputs, outputs, contents of state
    variables, and let definitions: everything that is expanded when
    translating the meta-logic to the base logic. *)
type msymb = Symbols.macro isymb

(*------------------------------------------------------------------*)
(** {3 Pretty printing} *)

val pp_nsymb  : Format.formatter -> nsymb      -> unit
val pp_nsymbs : Format.formatter -> nsymb list -> unit

val pp_msymb_s : Format.formatter -> Symbols.macro -> unit
val pp_msymb   : Format.formatter -> msymb         -> unit

val pp_fname : Format.formatter -> Symbols.fname -> unit

(*------------------------------------------------------------------*)
(** {2 Terms}

  In this module {!term} describe both terms and formulas of the meta-logic. *)

(** components of diff operators. *)
type proj
type projs = proj list

module Mproj : Map.S with type key = proj
module Sproj : Set.S with type elt = proj

val pp_proj  : Format.formatter -> proj -> unit
val pp_projs : Format.formatter -> projs -> unit
  
(** We use strings to identify components of diff operators. *)
val proj_from_string : string -> proj
val proj_to_string   : proj -> string

val left_proj  : proj
val right_proj : proj

(*------------------------------------------------------------------*)
(** We allow users to write [diff(t1,t2)] as well as [diff(lbl1:t1,lbl2:t2)]
    and even [diff(l1:t1,l2:t2,_:t)] and keep trace of this structure in
    terms in order to display them back similarly.
    TODO for simplicity we allow only a simple style for now *)
type 'a diff_args =
  | Explicit of (proj * 'a) list

(*------------------------------------------------------------------*)
type quant = ForAll | Exists | Seq | Lambda

val pp_quant : Format.formatter -> quant -> unit

(*------------------------------------------------------------------*)
type term = private
  | App    of term * term list
  | Fun    of Symbols.fname * Type.ftype * term list
  | Name   of nsymb * term list
  | Macro  of msymb * term list * term

  | Action of Symbols.action * term list

  | Var of Vars.var

  | Tuple of term list
  | Proj of int * term

  | Diff of term diff_args

  | Find of Vars.var list * term * term * term 

  | Quant of quant * Vars.var list * term 
             
type t = term

(** Structural comparison of terms. *)
val compare : t -> t -> int

type terms = term list

val hash : term -> int

val equal : term -> term -> bool

(*------------------------------------------------------------------*)
(** Does not recurse. *)
val tmap       : (term -> term) -> term -> term
val titer      : (term -> unit) -> term -> unit
val tfold      : (term -> 'a -> 'a) -> term -> 'a -> 'a
val tmap_fold  : ('b -> term -> 'b * term) -> 'b -> term -> 'b * term
val texists    : (term -> bool) -> term -> bool 
val tforall    : (term -> bool) -> term -> bool 

(*------------------------------------------------------------------*)
(** {2 Literals} *)

module Lit : sig
  type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
  type ord_eq = [ `Eq | `Neq ]

  val pp_ord : Format.formatter -> ord -> unit

  type ('a,'b) _atom = 'a * 'b * 'b

  type xatom = 
    | Comp    of (ord,term) _atom
    | Happens of term
    | Atom    of term           (* arbitrary atom, of type [Type.tboolean] *)

  type literal = [`Neg | `Pos] * xatom

  type literals = literal list

  (** Type of compared elements. *)
  val ty_xatom : xatom -> Type.ty

  (** Type of compared elements. *)
  val ty  : literal -> Type.ty

  val pp  : Format.formatter -> literal  -> unit
  val pps : Format.formatter -> literals -> unit

  val neg : literal -> literal

  val disjunction_to_literals : term -> literal list option

  val form_to_xatom   : term ->   xatom option
  val form_to_literal : term -> literal option

  (** Given a formula, return a list of literals which is either
      entailed by the formula, or equivalent to the formula. *)
  val form_to_literals :
    term -> [`Entails of literal list | `Equiv of literal list]

  val xatom_to_form : xatom   -> term
  val lit_to_form   : literal -> term
end

(*------------------------------------------------------------------*)
(** {2 Pretty-printer and cast} *)

(** Additional printing information *)
type pp_info

val default_pp_info : pp_info

val pp     :             Format.formatter -> term -> unit
val _pp    : dbg:bool -> Format.formatter -> term -> unit
val pp_dbg :             Format.formatter -> term -> unit

val pp_with_info : pp_info -> Format.formatter -> term -> unit

(*------------------------------------------------------------------*)
val ty  : ?ty_env:Type.Infer.env -> term -> Type.ty

(*------------------------------------------------------------------*)
(** [get_vars t] returns the free variables of [t].
  * The returned list is guaranteed to have no duplicate elements. *)
val get_vars : term -> Vars.var list

(** [has_var v t] returns true iff [v] occurs as a free var in [t] *)
val has_var : Vars.var -> term -> bool
  
(** Free variables of a term. *)
val fv  : term -> Sv.t
val fvs : terms -> Sv.t

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

val subst_support : subst -> Sv.t

val subst_binding : Vars.var -> subst -> Vars.var * subst

(** term substitution *)
val subst : subst -> term -> term

(** substitute type variables *)
val tsubst : Type.tsubst -> term -> term

(** [subst_var s v] returns [v'] if substitution [s] maps [v] to [Var v'],
    and [v] if the variable is not in the domain of the substitution. *)
val subst_var : subst -> Vars.var -> Vars.var

val subst_vars : subst -> Vars.vars -> Vars.vars

(** [subst_macros_ts table l ts t] replaces [ts] by [pred(ts)] in the term [t]
  * if [ts] is applied to a state macro whose name is NOT in [l]. *)
val subst_macros_ts : Symbols.table -> string list -> term -> term -> term

val subst_projs : (proj * proj) list -> term -> term 

(*------------------------------------------------------------------*)
val refresh_vars        : (Vars.var     ) list -> (Vars.var     ) list * subst
val refresh_vars_w_info : (Vars.var * 'a) list -> (Vars.var * 'a) list * subst

(** Add variables in an existing environment, renaming them if necessary. *)
val add_vars_env :
  'a Vars.genv -> (Vars.var * 'a) list ->
  'a Vars.genv * Vars.var list * esubst list

val add_vars_simpl_env :
  Vars.simpl_env -> Vars.var list ->
  Vars.simpl_env * Vars.var list * esubst list

(*------------------------------------------------------------------*)
(** {2 Builtins function symbols} *)

val empty : term
val init : term

val in_macro    : msymb
val out_macro   : msymb
val frame_macro : msymb
val cond_macro  : msymb
val exec_macro  : msymb

val f_happens : Symbols.fname

val f_pred : Symbols.fname

val f_true  : Symbols.fname
val f_false : Symbols.fname
val f_and   : Symbols.fname
val f_or    : Symbols.fname
val f_impl  : Symbols.fname
val f_iff   : Symbols.fname
val f_not   : Symbols.fname
val f_ite   : Symbols.fname

val f_eq  : Symbols.fname
val f_neq : Symbols.fname
val f_leq : Symbols.fname
val f_lt  : Symbols.fname
val f_geq : Symbols.fname
val f_gt  : Symbols.fname

val f_diff : Symbols.fname

val f_succ : Symbols.fname

val f_att : Symbols.fname

val f_fail : Symbols.fname

val f_xor  : Symbols.fname
val f_zero : Symbols.fname

val f_pair : Symbols.fname
val f_fst  : Symbols.fname
val f_snd  : Symbols.fname

val f_of_bool : Symbols.fname

val f_len    : Symbols.fname
val f_zeroes : Symbols.fname

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors} *)

module Smart : sig
  (** {3 Constructors} *)
  val mk_true  : term
  val mk_false : term

  val mk_eq  : ?simpl:bool -> term -> term -> term
  val mk_neq : ?simpl:bool -> term -> term -> term
  val mk_leq :                term -> term -> term
  val mk_geq :                term -> term -> term
  val mk_lt  : ?simpl:bool -> term -> term -> term
  val mk_gt  : ?simpl:bool -> term -> term -> term

  val mk_not   : ?simpl:bool -> term              -> term
  val mk_and   : ?simpl:bool -> term      -> term -> term
  val mk_ands  : ?simpl:bool -> term list         -> term
  val mk_or    : ?simpl:bool -> term      -> term -> term
  val mk_ors   : ?simpl:bool -> term list         -> term
  val mk_impl  : ?simpl:bool -> term      -> term -> term
  val mk_impls : ?simpl:bool -> term list -> term -> term

  val mk_forall : ?simpl:bool -> Vars.vars -> term -> term
  val mk_exists : ?simpl:bool -> Vars.vars -> term -> term

  (** Local terms do not take tags.
      By convention, we require that the tag [Vars.Tag.ltag] is 
      used for local terms. *)
  val mk_forall_tagged : ?simpl:bool -> Vars.tagged_vars -> term -> term
  val mk_exists_tagged : ?simpl:bool -> Vars.tagged_vars -> term -> term

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  (*------------------------------------------------------------------*)
  val destr_neq : term -> (term * term) option
  val destr_eq  : term -> (term * term) option
  val destr_leq : term -> (term * term) option
  val destr_lt  : term -> (term * term) option

  (*------------------------------------------------------------------*)
  val destr_false : term ->         unit  option
  val destr_true  : term ->         unit  option
  val destr_not   : term ->         term  option
  val destr_and   : term -> (term * term) option
  val destr_iff   : term -> (term * term) option

  (*------------------------------------------------------------------*)
  val destr_or   : term -> (term * term) option
  val destr_impl : term -> (term * term) option

  (*------------------------------------------------------------------*)
  val destr_forall_tagged  : term -> (Vars.tagged_vars * term) option
  val destr_forall1_tagged : term -> (Vars.tagged_var  * term) option
  val destr_exists_tagged  : term -> (Vars.tagged_vars * term) option
  val destr_exists1_tagged : term -> (Vars.tagged_var  * term) option

  val destr_forall  : term -> (Vars.vars * term) option
  val destr_forall1 : term -> (Vars.var  * term) option
  val destr_exists  : term -> (Vars.vars * term) option
  val destr_exists1 : term -> (Vars.var  * term) option

  (*------------------------------------------------------------------*)
  val is_false  : term -> bool
  val is_true   : term -> bool
  val is_not    : term -> bool
  val is_zero   : term -> bool
  val is_and    : term -> bool
  val is_or     : term -> bool
  val is_impl   : term -> bool
  val is_iff    : term -> bool
  val is_forall : term -> bool
  val is_exists : term -> bool

  (*------------------------------------------------------------------*)
  val is_neq : term -> bool
  val is_eq  : term -> bool
  val is_leq : term -> bool
  val is_lt  : term -> bool

  (*------------------------------------------------------------------*)
  (** left-associative *)
  val destr_ands  : int -> term -> term list option
  val destr_ors   : int -> term -> term list option
  val destr_impls : int -> term -> term list option

  (*------------------------------------------------------------------*)
  val decompose_forall : term -> Vars.var list * term 
  val decompose_exists : term -> Vars.var list * term

  (*------------------------------------------------------------------*)
  val decompose_forall_tagged : term -> Vars.tagged_var list * term 
  val decompose_exists_tagged : term -> Vars.tagged_var list * term

  (*------------------------------------------------------------------*)
  val decompose_ands  : term -> term list
  val decompose_ors   : term -> term list
  val decompose_impls : term -> term list

  val decompose_impls_last : term -> term list * term
end

include module type of Smart

(*------------------------------------------------------------------*)
(** {3 Smart constructors: terms} *)

val mk_pred    : term -> term
val mk_var     : Vars.var -> term
val mk_vars    : Vars.var list -> term list
val mk_action  : Symbols.action -> term list -> term
val mk_tuple   : term list -> term
val mk_app     : term -> term list -> term
val mk_proj    : int -> term -> term
val mk_name    : nsymb -> term list -> term
val mk_macro   : msymb -> term list -> term -> term
val mk_diff    : (proj * term) list -> term

val mk_find : ?simpl:bool -> Vars.var list -> term -> term -> term -> term

val mk_quant : ?simpl:bool -> quant -> Vars.vars -> term -> term
  
val mk_iff   : ?simpl:bool -> term -> term -> term
  
(*------------------------------------------------------------------*)
val mk_fun0 : Symbols.fname -> Type.ftype -> term list -> term

val mk_fun : Symbols.table -> Symbols.fname -> term list -> term

(** Declare a function of arity one (all arguments are grouped 
    into a tuple). *)
val mk_fun_tuple : Symbols.table -> Symbols.fname -> term list -> term

(*------------------------------------------------------------------*)
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

val mk_neqs : ?simpl:bool -> terms -> terms -> term
val mk_eqs  : ?simpl:bool -> terms -> terms -> term

val mk_atom : Lit.ord -> term -> term -> term
val mk_happens : term -> term

val mk_seq    : ?simpl:bool -> Vars.vars -> term -> term
val mk_lambda : ?simpl:bool -> Vars.vars -> term -> term

(*------------------------------------------------------------------*)
(** {3 Destructors} *)

val is_binder : term -> bool

val is_macro  : term -> bool

val is_name : term -> bool

val destr_var : term -> Vars.var option

val destr_tuple : term -> term list option
val destr_proj : term -> (int * term) option

val is_var   : term -> bool
val is_tuple : term -> bool
val is_proj  : term -> bool

(*------------------------------------------------------------------*)
val destr_action : term -> (Symbols.action * term list) option

(*------------------------------------------------------------------*)
val destr_pair : term -> (term * term) option

(*------------------------------------------------------------------*)
(** {2 Simplification} *)

val not_simpl : term -> term

(*------------------------------------------------------------------*)
(** {2 Sets and Maps } *)

module St : Set.S with type elt = term
module Mt : Map.S with type key = term

(*------------------------------------------------------------------*)
(** {2 Multi-terms} *)

val project1    : proj         -> term -> term
val project     : projs        -> term -> term
val project_opt : projs option -> term -> term 
  
(** Push topmost diff-operators just enough to expose the common
    topmost constructor of the two projections of a biterm, if possible.

    If the returned biterm starts with a diff, then its immediate
    subterms have topmost different constructors, and they do not
    start with diffs themselves.

    TODO: What is the constraint below used for?
    Macros with different timestamps do not count as a common
    constructor: [head_normal_biterm (Diff(Macro(m,l,ts),Macro(m,l,ts')))]
    will be [Diff(Macro(m,l,ts),Macro(m,l,ts'))] and not
    [Macro(m,l,Diff(ts,ts'))]. *)
val head_normal_biterm : term -> term

val simple_bi_term : term -> term

(** Same as [simple_bi_term], but does not try to normalize try-finds. 
    Ad-hoc fix to keep diffeq tactic working properly. 
    FIXME: remove it. *)
val simple_bi_term_no_alpha_find : term -> term

val combine : (proj * term) list -> term

(** All projections of the term are names. *)
val diff_names : term -> bool

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

(*------------------------------------------------------------------*)
(** {2 Term heads} *)

type term_head =
  | HApp
  | HExists
  | HForAll
  | HSeq
  | HLambda
  | HTuple
  | HProj
  | HFind
  | HFun   of Symbols.fname 
  | HMacro of Symbols.macro 
  | HName  of Symbols.name  
  | HDiff
  | HVar
  | HAction

val pp_term_head : Format.formatter -> term_head -> unit

val get_head : term -> term_head

module Hm : Map.S with type key = term_head

(*------------------------------------------------------------------*)
(** {2 Patterns} *)

(** A pattern is a list of free type variables, a term [t] and a subset
    of [t]'s free variables that must be matched.
    The free type variables must be inferred. *)
type 'a pat = {
  pat_tyvars : Type.tvars;
  pat_vars   : (Vars.var * Vars.Tag.t) list;
  pat_term   : 'a;
}

val project_tpat     : projs        -> term pat -> term pat
val project_tpat_opt : projs option -> term pat -> term pat

(** Make a pattern out of a formula: all universally quantified variables
    are added to [pat_vars]. *)
val pat_of_form : term -> term pat

(*------------------------------------------------------------------*)
(** {2 Misc} *)

exception AlphaFailed

(** [alpha_conv ~subst t1 t2] check that [t1] and [t2] are 
    alpha-convertible.
    - [subst] optional substitution from [t2] variables to [t1] 
      variables. *)
val alpha_conv : ?subst:subst -> term -> term -> bool 

(** Process binder variables during alpha-renaming, updating the
    alpha-renaming substitution (see [alpha_conv]).
    Raise if alpha-conversion fails. *)
val alpha_bnds : subst -> Vars.vars -> Vars.vars -> subst 



