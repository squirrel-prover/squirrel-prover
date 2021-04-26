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
    
val parse_p_ty0 : Symbols.table -> Type.tvar list -> p_ty -> Type.ety 

val parse_p_ty : 
  Symbols.table -> Type.tvar list -> p_ty -> 'a Type.kind -> 'a Type.ty 

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
  | Tinit
  | Tpred of term
  | Diff  of term * term
  | Seq   of lsymb list * term
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
                 
  | Compare of Term.ord * term * term
  | Happens of term list
  | ForAll  of bnds * term
  | Exists  of bnds * term

and term = term_i L.located

type formula = term

val pp_i : Format.formatter -> term_i -> unit
val pp   : Format.formatter -> term   -> unit

val equal : term -> term -> bool

(*------------------------------------------------------------------*)
(** {2 Declaration of new symbols} *)


(** Declare a new function symbol of type message->message->message, * which
    satisfies PRF, and thus collision-resistance and EUF. *)
val declare_hash :
  Symbols.table ->
  ?index_arity:int ->
  ?m_ty:Type.message Type.ty ->
  ?k_ty:Type.message Type.ty ->
  ?h_ty:Type.message Type.ty ->
  lsymb ->
  Symbols.table

(** Asymmetric encryption function symbols are defined by the triplet
    (enc,dec,pk).
    It models an authenticated encryption. *)
val declare_aenc :
  Symbols.table ->
  ?ptxt_ty:Type.message Type.ty ->
  ?ctxt_ty:Type.message Type.ty ->
  ?rnd_ty:Type.message Type.ty ->
  ?sk_ty:Type.message Type.ty ->
  ?pk_ty:Type.message Type.ty ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It models an authenticated encryption. *)
val declare_senc :
  Symbols.table ->
  ?ptxt_ty:Type.message Type.ty ->
  ?ctxt_ty:Type.message Type.ty ->
  ?rnd_ty:Type.message Type.ty ->
  ?k_ty:Type.message Type.ty ->
  lsymb -> lsymb ->
  Symbols.table

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It models an authenticated encryption, jointly secure with hashes of the key.*)
val declare_senc_joint_with_hash :
  Symbols.table ->
  ?ptxt_ty:Type.message Type.ty ->
  ?ctxt_ty:Type.message Type.ty ->
  ?rnd_ty:Type.message Type.ty ->
  ?k_ty:Type.message Type.ty ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table

(** A signature is defined by a triplet, corresponding to (sign,checksign,pk).
    It satisfies EUF. *)
val declare_signature :
  Symbols.table ->
  ?m_ty:Type.message Type.ty ->
  ?sig_ty:Type.message Type.ty ->
  ?check_ty:Type.message Type.ty ->
  ?sk_ty:Type.message Type.ty ->
  ?pk_ty:Type.message Type.ty ->
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
  Symbols.table -> (Term.state * Term.message) list

(** [declare_abstract n i m] declares a new function symbol
  * of type [index^i -> message^m -> message]. *)
val declare_abstract :
  Symbols.table -> 
  index_arity:int ->
  ty_args:Type.tvar list ->
  in_tys:Type.message Type.ty list ->
  out_ty:Type.message Type.ty ->
  lsymb ->
  Symbols.table

(* (** [declare_macro n [(x1,s1);...;(xn;sn)] s t] a macro symbol [s]
 *   * of type [s1->...->sn->s]
 *   * such that [s(t1,...,tn)] expands to [t\[x1:=t1,...,xn:=tn\]]. *)
 * val declare_macro :
 *   Symbols.table -> lsymb -> bnds -> p_ty -> term
 *   -> Symbols.table *)

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
  | Type_error           of term_i * Type.ety
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
  | BadPty               of Type.ekind list
      
type conversion_error = L.t * conversion_error_i

exception Conv of conversion_error

val pp_error :
  (Format.formatter -> L.t -> unit) ->
  Format.formatter -> conversion_error -> unit

type env = (string * Type.ety) list

val check : 
  Symbols.table -> ?local:bool -> Type.Infer.env -> env -> term -> Type.ety
  -> unit

val check_state : Symbols.table -> lsymb -> int -> Type.tmessage

(* Returns true if the given function names corresponds to some associated
   checksign and pk functions, returns Some sign, where sign is the
   corresponding signature. Else, returnes None. *)
val check_signature :
  Symbols.table -> Term.fname -> Term.fname -> Term.fname option

(*------------------------------------------------------------------*)
(** {2 Conversions}
  * Convert terms inside the theory to terms of the prover. *)

val subst : term -> (string * term_i) list -> term

type esubst = ESubst : string * 'a Term.term -> esubst

type subst = esubst list

val subst_of_env : Vars.env -> subst

val parse_subst :
  Symbols.table -> Vars.env -> Vars.evar list -> term list -> Term.subst

val pp_subst : Format.formatter -> subst -> unit

val convert_index : Symbols.table -> subst -> term -> Vars.index

(** Conversion context.
  * - [InGoal]: we are converting a term in a goal (or tactic). All
  *   timestamps must be explicitely given.
  * - [InProc ts]: we are converting a term in a process at an implicit
  *   timestamp [ts]. *)
type conv_cntxt =
  | InProc of Term.timestamp
  | InGoal

type conv_env = { table : Symbols.table;
                  cntxt : conv_cntxt; }

(** converts and infer the type (must be a subtype of Message). *)
val convert_i : 
  ?ty_env:Type.Infer.env -> conv_env -> subst -> term -> 
  Term.message * Type.tmessage

val convert : 
  ?ty_env:Type.Infer.env -> conv_env -> subst -> term -> 'a Type.ty
  -> 'a Term.term

(** Existantial type wrapping a converted term and its sort.
    The location is the location of the original [Theory.term].  *)
type eterm = ETerm : 'a Type.ty * 'a Term.term * L.t -> eterm

(** Convert a term to any sort (tries sequentially all conversions).
    Should return the most precise sort (i.e. [Boolean] before [Message]). *)
val econvert : conv_env -> subst -> term -> eterm option

(** [find_app_terms t names] returns the sublist of [names] for which there
  * exists a subterm [Theory.App(name,_)] or [Theory.AppAt(name,_,_)] in the
  * term [t]. *)
val find_app_terms : term -> string list -> string list
