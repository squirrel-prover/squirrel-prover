(** Terms for the Meta-BC logic.
  *
  * This module describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

module Sv = Vars.Sv
              
(*------------------------------------------------------------------*)
(** {2 Symbols}
  *
  * We have function, name and macro symbols. Each symbol
  * can then be indexed. *)

(** Ocaml type of a typed index symbol.
    Invariant: [s_typ] do not contain tvar or univars *)
type ('a,'b) isymb = private { 
  s_symb    : 'a;
  s_indices : Vars.index list;
  s_typ     : 'b; 
}

val mk_isymb : 'a -> Type.tmessage -> Vars.index list -> ('a,Type.tmessage) isymb

(** Names represent random values of length the security parameter. *)

type name = Symbols.name Symbols.t
type nsymb = (name, Type.tmessage) isymb

(** Function symbols, may represent primitives or abstract functions. *)

type fname = Symbols.fname Symbols.t
type fsymb = fname * Vars.index list

(** Macros are used to represent inputs, outputs, contents of state
  * variables, and let definitions: everything that is expanded when
  * translating the meta-logic to the base logic. *)

type mname    = Symbols.macro Symbols.t
type msymb = (mname, Type.tmessage) isymb

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
(** {2 Terms} *)

(** ['a term] is the type of terms of sort ['a].
  * Since index terms and just variables, and booleans are a subtype
  * of message, we are only interested in sorts [timestamp] and
  * [message]. *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

val pp_ord   : Format.formatter -> ord -> unit
  
type ('a,'b) _atom = 'a * 'b * 'b

type generic_atom = [
  | `Message of (ord_eq,Type.message term) _atom
  | `Timestamp of (ord,Type.timestamp term) _atom
  | `Index of (ord_eq,Vars.index) _atom
  | `Happens of Type.timestamp term
]
and _ term = private
  | Fun    : fsymb * Type.ftype * Type.message term list -> Type.message term
  | Name   : nsymb -> Type.message term

  | Macro  :
      msymb * Type.message term list * Type.timestamp term
      -> Type.message term

  | Seq    : Vars.evar list * Type.message term -> Type.message term
  | Pred   : Type.timestamp term -> Type.timestamp term
  | Action : Symbols.action Symbols.t * Vars.index list -> Type.timestamp term
  | Var    : 'a Vars.var -> 'a term

  | Diff : 'a term * 'a term -> 'a term

  | Find :
      Vars.index list * Type.message term *
      Type.message term * Type.message term ->
      Type.message term

  | Atom : generic_atom -> Type.message term

  | ForAll : Vars.evar list * Type.message term -> Type.message term
  | Exists : Vars.evar list * Type.message term -> Type.message term

type 'a t = 'a term

val hash : 'a term -> int

(*------------------------------------------------------------------*)
type message  = Type.message term
type messages = message list

type timestamp  = Type.timestamp term
type timestamps = timestamp list

(*------------------------------------------------------------------*)
type eterm = ETerm : 'a term -> eterm

(** Does not recurse. *)
val tmap       : (eterm -> eterm) -> 'a term -> 'a term 
val titer      : (eterm -> unit) -> 'a term -> unit
val tfold      : (eterm -> 'a -> 'a) -> 'b term -> 'a -> 'a
val tmap_fold  : ('b -> eterm -> 'b * eterm) -> 'b -> 'a term -> 'b * 'a term 

(*------------------------------------------------------------------*)
(** {2 Subset of all atoms} *)
(** (the subsets are not disjoint). *)

type message_atom = [ `Message of (ord_eq,Type.message term) _atom]

type index_atom = [ `Index of (ord_eq,Vars.index) _atom]
                    
type trace_atom = [
  | `Timestamp of (ord,timestamp) _atom
  | `Index     of (ord_eq,Vars.index) _atom
  | `Happens   of Type.timestamp term
]

type trace_eq_atom = [
  | `Timestamp of (ord_eq,timestamp)  _atom
  | `Index     of (ord_eq,Vars.index) _atom
]

type eq_atom = [
  | `Message   of (ord_eq, message) _atom
  | `Timestamp of (ord_eq, timestamp) _atom
  | `Index     of (ord_eq, Vars.index) _atom
]

(*------------------------------------------------------------------*)
(** Literals. *)

type literal = [`Neg | `Pos] * generic_atom

type eq_literal = [`Pos | `Neg] * eq_atom

type trace_literal = [`Pos | `Neg] * trace_atom

val pp_literal  : Format.formatter -> literal      -> unit
val pp_literals : Format.formatter -> literal list -> unit

val pp_trace_literal  : Format.formatter -> trace_literal      -> unit
val pp_trace_literals : Format.formatter -> trace_literal list -> unit

val neg_lit : literal -> literal 

val neg_trace_lit : trace_literal -> trace_literal 

val disjunction_to_literals : message -> literal list option

(** Given a formula, return a list of literals which is either
    entailed by the formula, or equivalent to the formula. *)
val form_to_literals :
  message -> [`Entails of literal list | `Equiv of literal list]
    
(*------------------------------------------------------------------*)
(** {2 Higher-order terms} *)

type hterm = 
  | Lambda of Vars.evars * message

val pp_hterm : Format.formatter -> hterm -> unit

(*------------------------------------------------------------------*)
(** {2 Pretty-printer and cast} *)

(** Additional printing information *)
type pp_info

val default_pp_info : pp_info

val pp : Format.formatter -> 'a term -> unit

val pp_with_info : pp_info -> Format.formatter -> 'a term -> unit

(*------------------------------------------------------------------*)
val kind : 'a term -> 'a Type.kind
    
val ty  : ?ty_env:Type.Infer.env -> 'a term -> 'a Type.ty
val ety : ?ty_env:Type.Infer.env -> 'a term -> Type.ety

(*------------------------------------------------------------------*)
exception Uncastable

(** [cast k t] checks that [t] can be seen as a message of kind [k].
    @raise Uncastable if the term cannot be cast.*)
val cast : 'a Type.kind -> 'b term -> 'a term

(*------------------------------------------------------------------*)
(** [get_vars t] returns the free variables of [t].
  * The returned list is guaranteed to have no duplicate elements. *)
val get_vars : 'a term -> Vars.evar list

(** [fv t] returns the free variables of [t]. *)
val fv : 'a term -> Sv.t

val f_triv : message -> bool

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

(** Substitutions for all purpose, applicable to terms and timestamps.
  * TODO unusually, we map terms to terms and not just variables to terms;
  * this is used somewhere... but I forgot where *)
type esubst = ESubst : 'a term * 'a term -> esubst

type subst = esubst list

val pp_subst : Format.formatter -> subst -> unit

val is_var_subst : subst -> bool

val subst_support : subst -> Sv.t

val subst_binding : Vars.evar -> subst -> Vars.evar * subst 

(** term substitution *)
val subst : subst -> 'a term -> 'a term

(** substitute type variables *)
val tsubst : Type.tsubst -> 'a term -> 'a term

val tsubst_ht : Type.tsubst -> hterm -> hterm

(** [subst_var s v] returns [v'] if substitution [s] maps [v] to [Var v'],
  * and [v] if the variable is not in the domain of the substitution.
  * @raise Substitution_error if [v] is mapped to a non-variable term in [s]. *)
val subst_var  : subst -> 'a Vars.var -> 'a Vars.var

val subst_evar : subst -> Vars.evar   -> Vars.evar

(** Substitute indices in an indexed symbols. *)
val subst_isymb : subst -> ('a,'b) isymb -> ('a,'b) isymb

(** [subst_macros_ts table l ts t] replaces [ts] by [pred(ts)] in the term [t]
  * if [ts] is applied to a state macro whose name is NOT in [l]. *)
val subst_macros_ts : 
  Symbols.table -> 
  string list -> Type.timestamp term -> 'a term -> 'a term

(*------------------------------------------------------------------*)
type refresh_arg = [`Global | `InEnv of Vars.env ref ]

val refresh_vars  : refresh_arg -> 'a Vars.vars -> 'a Vars.vars * esubst list
val erefresh_vars : refresh_arg ->   Vars.evars ->   Vars.evars * esubst list

val refresh_vars_env :
  Vars.env -> 'a Vars.var list -> Vars.env * 'a Vars.var list * esubst list

val erefresh_vars_env :
  Vars.env -> Vars.evar list -> Vars.env * Vars.evar list * esubst list
 
(*------------------------------------------------------------------*)
val apply_ht : hterm -> eterm list -> hterm

(*------------------------------------------------------------------*)
(** {2 Builtins function symbols} *)

val empty : message 
val init : timestamp

val in_macro    : msymb
val out_macro   : msymb
val frame_macro : msymb
val cond_macro  : msymb
val exec_macro  : msymb

val f_true   : fsymb
val f_false  : fsymb
val f_and    : fsymb
val f_impl   : fsymb
val f_or     : fsymb
val f_not    : fsymb
val f_ite    : fsymb

val f_diff   : fsymb

val f_succ   : fsymb

val f_att    : fsymb

val f_fail   : fsymb

val f_xor    : fsymb
val f_zero   : fsymb

val f_pair   : fsymb
val f_fst    : fsymb
val f_snd    : fsymb

val f_of_bool   : fsymb

val f_len    : fsymb
val f_zeroes : fsymb
  
(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors} *)

(** Module type for smart constructors and destructors on first-order formulas,
    where the type is abstracted. Instantiated by both [Term] and [Equiv]. *)
module type SmartFO = sig
  type form

  (** {3 Constructors} *)
  val mk_true    : form
  val mk_false   : form

  val mk_not   : ?simpl:bool -> form              -> form
  val mk_and   : ?simpl:bool -> form      -> form -> form
  val mk_ands  : ?simpl:bool -> form list         -> form
  val mk_or    : ?simpl:bool -> form      -> form -> form
  val mk_ors   : ?simpl:bool -> form list         -> form
  val mk_impl  : ?simpl:bool -> form      -> form -> form
  val mk_impls : ?simpl:bool -> form list -> form -> form

  val mk_forall : ?simpl:bool -> Vars.evars -> form -> form
  val mk_exists : ?simpl:bool -> Vars.evars -> form -> form

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  val destr_forall : form -> (Vars.evar list * form) option
  val destr_exists : form -> (Vars.evar list * form) option

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
  val is_and    : form -> bool
  val is_or     : form -> bool
  val is_impl   : form -> bool
  val is_forall : form -> bool
  val is_exists : form -> bool
  val is_matom  : form -> bool

  (*------------------------------------------------------------------*)
  (** left-associative *)
  val destr_ands  : int -> form -> form list option
  val destr_ors   : int -> form -> form list option
  val destr_impls : int -> form -> form list option

  (*------------------------------------------------------------------*)
  val destr_matom : form -> (ord_eq * message * message) option 

  (*------------------------------------------------------------------*)
  val decompose_forall : form -> Vars.evar list * form
  val decompose_exists : form -> Vars.evar list * form

  (*------------------------------------------------------------------*)
  val decompose_ands  : form -> form list 
  val decompose_ors   : form -> form list 
  val decompose_impls : form -> form list 

  val decompose_impls_last : form -> form list * form
end

module Smart : SmartFO with type form = message

include module type of Smart

(*------------------------------------------------------------------*)
(** {3 Smart constructors: terms} *)

val mk_pred   : timestamp -> timestamp
val mk_var    : 'a Vars.var -> 'a term
val mk_action : Symbols.action Symbols.t -> Vars.index list -> timestamp
val mk_name   : nsymb -> message
val mk_macro  : msymb -> message list -> timestamp -> message
val mk_diff   : 'a term -> 'a term -> 'a term

val mk_find : Vars.index list -> message -> message -> message -> message


(*------------------------------------------------------------------*)
val mk_fun0 : fsymb -> Type.ftype -> message list -> message

val mk_fun :
  Symbols.table ->
  fname ->
  Vars.index list ->
  message list ->
  message
    
val mk_zero    : message
val mk_fail    : message
val mk_len     : message -> message
val mk_zeroes  : message -> message
val mk_of_bool : message -> message
val mk_pair    : message -> message -> message

val mk_witness : Type.tmessage -> message

(*------------------------------------------------------------------*)
(** {3 Smart constructors: messages} *)

val mk_ite : ?simpl:bool -> message -> message -> message -> message
  
val mk_timestamp_leq : timestamp -> timestamp -> message

val mk_indices_neq : Vars.index list -> Vars.index list -> message
val mk_indices_eq  : ?simpl:bool -> Vars.index list -> Vars.index list -> message

val mk_atom : ord -> 'a term -> 'b term -> message 
val mk_happens : timestamp -> message 
val mk_atom1 : generic_atom -> message 

val mk_seq0 : ?simpl:bool -> Vars.evars -> message -> message

(** Refresh variables *)
val mk_seq : Vars.env -> Vars.evars -> message -> message

(*------------------------------------------------------------------*)
(** {3 Destructors} *)

val is_binder : 'a term -> bool

val destr_var : 'a term -> 'a Vars.var option
    
(*------------------------------------------------------------------*)
val destr_action : 
  timestamp -> (Symbols.action Symbols.t * Vars.index list) option

(*------------------------------------------------------------------*)
val destr_pair : message -> (message * message) option


(*------------------------------------------------------------------*)
(** {2 Simplification} *)

val not_message_atom  : message_atom  -> message_atom
val not_index_atom    : index_atom    -> index_atom
val not_trace_eq_atom : trace_eq_atom -> trace_eq_atom

val not_simpl : message -> message

(** Check if a formula only depends on the trace model. *)
val is_pure_timestamp : message -> bool
  
(*------------------------------------------------------------------*)
(** {2 Sets and Maps } *)

module St : Set.S with type elt = eterm
module Mt : Map.S with type key = eterm

(*------------------------------------------------------------------*)
(** {2 Convert from bi-terms to terms}
  *
  * TODO Could we use a strong typing of [term] to make a static
  * distinction between biterms (general terms) and terms (terms
  * without diff operators)? *)

type projection = PLeft | PRight | PNone

val pp_projection : Format.formatter -> projection -> unit


(** Evaluate all diff operators wrt a projection.
  * If the projection is [None], the input term is returned unchanged.
  * Otherwise all diff operators are evaluated to the given
  * side and the returned term does not feature diff operators.
  * If the bi-term contains macros, and come from a bi-system, its
  * projection is only correctly interpreted if it is used inside
  * the projected system.
  * *)
val pi_term :  projection:projection -> 'a term -> 'a term

(** Evaluate topmost diff operators
  * for a given projection of a biterm.
  * For example [head_pi_term Left (diff(f(diff(a,b)),c))]
  * would be [f(diff(a,b))].
  * Macros are returned without suspended projections over them. *)
val head_pi_term : projection -> 'a term -> 'a term

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
val head_normal_biterm : 'a term -> 'a term

val make_bi_term : 'a term -> 'a term -> 'a term

(*------------------------------------------------------------------*)
(** {2 Matching information for error messages} *)

type match_info = 
  | MR_ok                         (* term matches *)
  | MR_check_st of message list   (* need to look at subterms *)
  | MR_failed                     (* term does not match *)

type match_infos = match_info Mt.t

val pp_match_info : Format.formatter -> match_info -> unit 

val pp_match_infos : Format.formatter -> match_infos -> unit 

val match_infos_to_pp_info : match_infos -> pp_info 
