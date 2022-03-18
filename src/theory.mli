(** This module defines terms and facts used during parsing,
  * functions to type-check them, and convert them to proper
  * terms and formulas of the logic. *)

module L = Location

type lsymb = string L.located

(*------------------------------------------------------------------*)
(** {2 Types } *)

type p_ty_i =
  | P_message
  | P_boolean
  | P_index  
  | P_timestamp
  | P_tbase of lsymb
  | P_tvar  of lsymb

type p_ty = p_ty_i L.located
    
val parse_p_ty : Env.t -> p_ty -> Type.ty 

val pp_p_ty : Format.formatter -> p_ty -> unit

(*------------------------------------------------------------------*)
(** Parsed binder *)
type bnd  = lsymb * p_ty

(** Parsed binders *)
type bnds = bnd list

(*------------------------------------------------------------------*)
(** {2 Terms}
  *
  * We define here terms used for parsing. Their variables are strings,
  * they are not attached to sorts. It will be the job of the typechecker
  * to make sure that types make sense, and of the conversion to replace
  * strings by proper sorted variables.
  *
  * Symbols cannot be disambiguated at parsing time, hence we use very
  * permissives [App] and [AppAt] constructors which represents
  * function applications, macros, variables, names etc. *)

type term_i =
  | Tpat  
  | Diff  of term * term
  | Seq   of bnds * term
  | Find  of lsymb list * term * term * term

  | App of lsymb * term list
  (** An application of a symbol to some arguments which as not been
    * disambiguated yet (it can be a name, a function symbol
    * application, a variable, ...)
    * [App(f,t1 :: ... :: tn)] is [f (t1, ..., tn)] *)

  | AppAt of lsymb * term list * term
  (** An application of a symbol to some arguments, at a given
    * timestamp.  As for [App _], the head function symbol has not been
    * disambiguated yet.
    * [AppAt(f,t1 :: ... :: tn,tau)] is [f (t1, ..., tn)\@tau] *)
                 
  | ForAll  of bnds * term
  | Exists  of bnds * term

and term = term_i L.located

type formula = term

val pp_i : Format.formatter -> term_i -> unit
val pp   : Format.formatter -> term   -> unit

val equal : term -> term -> bool

(*------------------------------------------------------------------*)
(** {2 Higher-order terms.} *)

(** For now, we need (and allow) almost no higher-order terms. *)
type hterm_i =
  | Lambda of bnds * term

type hterm = hterm_i L.located

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)

type equiv = term list 

type pquant = PForAll | PExists
              
type global_formula = global_formula_i Location.located

and global_formula_i =
  | PEquiv  of equiv
  | PReach  of formula
  | PImpl   of global_formula * global_formula
  | PAnd    of global_formula * global_formula
  | POr     of global_formula * global_formula
  | PQuant  of pquant * bnds * global_formula

(*------------------------------------------------------------------*)
(** {2 Declaration of new symbols} *)


(** Declare a new function symbol of type message->message->message, * which
    satisfies PRF, and thus collision-resistance and EUF. *)
val declare_hash :
  Symbols.table ->
  ?index_arity:int ->
  ?m_ty:Type.ty ->
  ?k_ty:Type.ty ->
  ?h_ty:Type.ty ->
  lsymb ->
  Symbols.table

(** DH assumption given by h on a group with generator gen, exponentiation exp, optionnally multiplication mult. *)
val declare_dh :
  Symbols.table ->
  Symbols.dh_hyp list ->
  ?group_ty:Type.ty ->
  ?exp_ty:Type.ty ->
  lsymb ->
  lsymb * Symbols.symb_type -> 
  (lsymb * Symbols.symb_type) option -> 
  Symbols.table

(** Asymmetric encryption function symbols are defined by the triplet
    (enc,dec,pk).
    It models an authenticated encryption. *)
val declare_aenc :
  Symbols.table ->
  ?ptxt_ty:Type.ty ->
  ?ctxt_ty:Type.ty ->
  ?rnd_ty:Type.ty ->
  ?sk_ty:Type.ty ->
  ?pk_ty:Type.ty ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It models an authenticated encryption. *)
val declare_senc :
  Symbols.table ->
  ?ptxt_ty:Type.ty ->
  ?ctxt_ty:Type.ty ->
  ?rnd_ty:Type.ty ->
  ?k_ty:Type.ty ->
  lsymb -> lsymb ->
  Symbols.table

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It models an authenticated encryption, jointly secure with hashes of the key.*)
val declare_senc_joint_with_hash :
  Symbols.table ->
  ?ptxt_ty:Type.ty ->
  ?ctxt_ty:Type.ty ->
  ?rnd_ty:Type.ty ->
  ?k_ty:Type.ty ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table

(** A signature is defined by a triplet, corresponding to (sign,checksign,pk).
    It satisfies EUF. *)
val declare_signature :
  Symbols.table ->
  ?m_ty:Type.ty ->
  ?sig_ty:Type.ty ->
  ?check_ty:Type.ty ->
  ?sk_ty:Type.ty ->
  ?pk_ty:Type.ty ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table

(** [declare_name n ndef] declares a new name of type
  * [index^i -> message]. *)
val declare_name : Symbols.table -> lsymb -> Symbols.name_def -> Symbols.table

(** [declare_state n [(x1,s1);...;(xn;sn)] s t] declares
    a new state symbol of type [s1->...->sn->s]
    where [si] is [index] and [s] is [message]
    such that value of [s(t1,...,tn)] for init timestamp
    expands to [t\[x1:=t1,...,xn:=tn\]]. *)
val declare_state : 
  Symbols.table -> lsymb -> bnds -> p_ty -> term -> Symbols.table
       
(** [get_init_states] returns all the initial values of declared state symbols,
    used to register the init action *)
val get_init_states :
  Symbols.table -> (Term.state * Term.term) list

(** [declare_abstract n i m] declares a new function symbol
  * of type [index^i -> message^m -> message]. *)
val declare_abstract :
  Symbols.table -> 
  index_arity:int ->
  ty_args:Type.tvar list ->
  in_tys:Type.ty list ->
  out_ty:Type.ty ->
  lsymb -> Symbols.symb_type ->
  Symbols.table

(*------------------------------------------------------------------*)
(** {2 Term builders } *)

val empty : L.t -> term

(** [var_i x] make a variable represented as [App (x,\[\])] *)
val var_i        : L.t -> string -> term_i
val var          : L.t -> string -> term
val var_of_lsymb : lsymb                -> term

val destr_var : term_i -> lsymb option

(*------------------------------------------------------------------*)
(** {2 Type-checking} *)

type conversion_error_i =
  | Arity_error          of string*int*int
  | Untyped_symbol       of string
  | Index_error          of string*int*int
  | Undefined            of string
  | UndefinedOfKind      of string * Symbols.namespace
  | Type_error           of term_i * Type.ty
  | Timestamp_expected   of term_i
  | Timestamp_unexpected of term_i
  (* | Untypable_equality   of term_i *)
  | Unsupported_ord      of term_i
  | String_expected      of term_i
  | Int_expected         of term_i
  | Tactic_type          of string
  | Index_not_var        of term_i
  | Assign_no_state      of string
  | BadNamespace         of string * Symbols.namespace
  | Freetyunivar
  | UnknownTypeVar       of string
  | BadPty               of Type.ty list
  | BadInfixDecl
  | PatNotAllowed
  | ExplicitTSInProc 
  | UndefInSystem of SystemExpr.t
    
type conversion_error = L.t * conversion_error_i

exception Conv of conversion_error

val conv_err : L.t -> conversion_error_i -> 'a
    
val pp_error :
  (Format.formatter -> L.t -> unit) ->
  Format.formatter -> conversion_error -> unit

val check : 
  Env.t -> ?local:bool -> ?pat:bool ->
  Type.Infer.env -> term -> Type.ty
  -> unit

val check_state : Symbols.table -> lsymb -> int -> Type.ty

(* Returns true if the given function names corresponds to some associated
   checksign and pk functions, returns Some sign, where sign is the
   corresponding signature. Else, returnes None. *)
val check_signature :
  Symbols.table -> Term.fname -> Term.fname -> Term.fname option

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

val subst : term -> (string * term_i) list -> term

type esubst = ESubst : string * Term.term -> esubst

type subst = esubst list

(*------------------------------------------------------------------*)
(** {2 Conversions}
  * Convert terms inside the theory to terms of the prover. *)

val parse_subst : Env.t -> Vars.var list -> term list -> Term.subst

(** Conversion context.
  * - [InGoal]: we are converting a term in a goal (or tactic). All
  *   timestamps must be explicitely given.
  * - [InProc ts]: we are converting a term in a process at an implicit
  *   timestamp [ts]. *)
type conv_cntxt =
  | InProc of Term.term
  | InGoal

type conv_env = { 
  env   : Env.t;
  cntxt : conv_cntxt; 
}

(** Converts and infer the type. *)
val convert : 
  ?ty:Type.ty ->
  ?ty_env:Type.Infer.env -> 
  ?pat:bool ->
  conv_env -> 
  term ->
  Term.term * Type.ty

val convert_p_bnds : Env.t -> bnds -> Env.t * Vars.var list

val convert_ht :
  ?ty_env:Type.Infer.env -> 
  ?pat:bool ->
  conv_env -> 
  hterm -> 
  Type.hty * Term.hterm

val convert_global_formula : conv_env -> global_formula -> Equiv.form

(** [find_app_terms t names] returns the sublist of [names] for which there
  * exists a subterm [Theory.App(name,_)] or [Theory.AppAt(name,_,_)] in the
  * term [t]. *)
val find_app_terms : term -> string list -> string list

(*------------------------------------------------------------------*)
(** {2 Proof terms} *)

(** proof term *)
type p_pt = {
  p_pt_head : lsymb;
  p_pt_args : p_pt_arg list;
  p_pt_loc  : L.t;
}

(** proof term argument *)
and p_pt_arg =
  | PT_term of term
  | PT_sub  of p_pt             (* sub proof term *)
  | PT_obl  of L.t              (* generate a proof obligation *)
