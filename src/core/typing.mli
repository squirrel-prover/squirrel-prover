(** This module defines terms and facts used during parsing,
    functions to type-check them, and convert them to proper
    terms and formulas of the logic. *)

module L  = Location
module SE = SystemExpr
module Mv = Vars.Mv
              
type lsymb = string L.located

(*------------------------------------------------------------------*)
(** {2 Types } *)

type ty_i =
  | P_message
  | P_boolean
  | P_index  
  | P_timestamp
  | P_tbase  of Symbols.p_path
  | P_tvar   of lsymb
  | P_fun    of ty * ty
  | P_tuple  of ty list
  | P_ty_pat 
             
and ty = ty_i L.located
    
val convert_ty : ?ty_env:Infer.env -> Env.t -> ty -> Type.ty 

(*------------------------------------------------------------------*)
(** Parsed binder *)
    
type bnd = lsymb * ty

type bnds = bnd list

(*------------------------------------------------------------------*)
(** Parser type for variables tags *)
type var_tags = lsymb list

(*------------------------------------------------------------------*)
(** Parsed binder with tags *)
    
type bnd_tagged = lsymb * (ty * var_tags)

type bnds_tagged = bnd_tagged list

(*------------------------------------------------------------------*)
(** Left value.
    Support binders with destruct, e.g. [(x,y) : bool * bool] *)
type lval =
  | L_var   of lsymb
  | L_tuple of lsymb list 

(** Extended binders (with variable tags) *)
type ext_bnd = lval * (ty * var_tags)
type ext_bnds = ext_bnd list

(*------------------------------------------------------------------*)
(** {2 Terms}
   
    We define here terms used for parsing. Their variables are strings,
    they are not attached to sorts. It will be the job of the typechecker
    to make sure that types make sense, and of the conversion to replace
    strings by proper sorted variables.
   
    Symbols cannot be disambiguated at parsing time, hence we use very
    permissives [App] and [AppAt] constructors which represents
    function applications, macros, variables, names etc. *)

type quant = Term.quant

type term_i =
  | Tpat

  | Int    of int L.located
  | String of string L.located

  | Diff  of term * term
  | Find  of bnds * term * term * term
  | Tuple of term list
  | Proj  of int L.located * term
  | Let   of lsymb * term * ty option * term
  | Symb  of Symbols.p_path * ty list option
  (** (symbole, optional type arguments) *)
  | App   of term * term list
  (** Application of a term to another. 
      [AppTerm (t, [t1 ... tn])] is [t t1 ... tn]. *)
  | AppAt of term * term
  (** An application of a symbol to special timestamp arguments.
      [AppAt(t1, t2)] is [t1 \@ t2] *)
  | Quant of quant * ext_bnds * term

and term = term_i L.located

(*------------------------------------------------------------------*)
val mk_symb : Symbols.p_path -> term 

val mk_app   : term -> term list -> term 
val mk_app_i : term -> term list -> term_i

val decompose_app : term -> term * term list

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)

(** global predicate application *)
type pred_app = {
  name    : Symbols.p_path;     (** predicate symbol *)
  se_args : SE.Parse.t list;    (** optional system arguments *)
  ty_args : ty list option;     (** optional type arguments *)
  args    : term list;          (** multi-term and term arguments *)
}

type equiv = term list 

type pquant = PForAll | PExists
              
type global_formula = global_formula_i Location.located

and global_formula_i =
  | PEquiv  of equiv * term option
  | PReach  of term * term option
  | PPred   of pred_app
  | PImpl   of global_formula * global_formula
  | PAnd    of global_formula * global_formula
  | POr     of global_formula * global_formula
  | PQuant  of pquant * bnds_tagged * global_formula
  | PLet    of lsymb * term * ty option * global_formula

(*------------------------------------------------------------------*)
(** {2 Any term: local or global} *)

type any_term = Global of global_formula | Local of term

(*------------------------------------------------------------------*)
(** {2 Declaration of new symbols} *)


(** Declare a new function symbol of type message->message->message, which
    satisfies PRF, and thus collision-resistance and EUF. *)
val declare_hash :
  Symbols.table ->
  ?m_ty:Type.ty ->
  ?k_ty:Type.ty ->
  ?h_ty:Type.ty ->
  lsymb ->
  Symbols.table

(** DH assumption given by h on a group with generator gen, exponentiation exp, 
    optionnally multiplication mult. *)
val declare_dh :
  Symbols.table ->
  Symbols.OpData.dh_hyp list ->
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
  lsymb -> lsymb -> Symbols.p_path ->
  Symbols.table

(** A signature is defined by a triplet, corresponding to (sign,checksign,pk).
    It satisfies EUF. *)
val declare_signature :
  Symbols.table ->
  ?m_ty:Type.ty ->
  ?sig_ty:Type.ty ->
  ?sk_ty:Type.ty ->
  ?pk_ty:Type.ty ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table
       
(** [declare_abstract n i m] declares a new function symbol
    of type [index^i -> message^m -> message]. *)
val declare_abstract :
  Symbols.table -> 
  ty_args:Type.tvar list ->
  in_tys:Type.ty list ->
  out_ty:Type.ty ->
  lsymb -> Symbols.symb_type ->
  Symbols.table

(** Sanity checks for a function symbol declaration. *)
val check_fun_symb :
  int ->                        (* number of arguments *)
  lsymb -> Symbols.symb_type -> unit
  
(*------------------------------------------------------------------*)
(** {2 Term builders } *)

val empty : L.t -> term

(** [var_i x] make a variable represented as [App (x,\[\])] *)
val var_i        : L.t -> string -> term_i
val var          : L.t -> string -> term

(*------------------------------------------------------------------*)
(** {2 Type-checking} *)

type conversion_error_i =
  | Arity_error          of string * int * int
  (** [string] unknown in optional namespace [npath] for kind [kind] *)
  | Type_error           of Term.term * Type.ty * Type.ty (* expected, got *)
  | Timestamp_expected   of string
  | Timestamp_unexpected of string
  | Tactic_type          of string
  | Assign_no_state      of string
  | BadSymbolKind        of string * Symbols.symbol_kind
  | Freetyunivar
  | UnknownTypeVar       of string
  | BadPty               of Type.ty list

  | BadTermProj          of int * int (* tuple length, given proj *)
  | NotTermProj

  | ExpectedTupleTy
  | BadTupleLength       of int * int (* expected, got *)

  | BadInfixDecl
  | PatNotAllowed
  | ExplicitTSInProc
  | UndefInSystem        of string * SE.t
  | MissingSystem
  | BadProjInSubterm     of Projection.t list * Projection.t list

  | Failure              of string

type conversion_error = L.t * conversion_error_i

exception Error of conversion_error

val error : L.t -> conversion_error_i -> 'a
    
val pp_error :
  (Format.formatter -> L.t -> unit) ->
  Format.formatter -> conversion_error -> unit

val check : 
  Env.t ->
  ?local:bool -> ?pat:bool ->
  ?system_info:SE.t Mv.t ->
  Infer.env -> Projection.t list ->
  term -> Type.ty ->
  unit

(* Returns true if the given function names corresponds to some associated
   checksign and pk functions, returns Some sign, where sign is the
   corresponding signature. Else, returnes None. *)
val check_signature :
  Symbols.table -> Symbols.fname -> Symbols.fname -> Symbols.fname option

(*------------------------------------------------------------------*)
(** {2 Conversions}
    Convert terms inside the theory to terms of the prover. *)

(** Conversion contexts.
    - [InGoal]: converting a term in a goal (or tactic). All
      timestamps must be explicitely given.
    - [InProc (projs, ts)]: converting a term in a process at an implicit
      timestamp [ts], with projections [projs]. *)
type conv_cntxt =
  | InProc of Projection.t list * Term.term
  | InGoal

(*------------------------------------------------------------------*)
type conv_env = { 
  env   : Env.t;
  cntxt : conv_cntxt; 
}

(*------------------------------------------------------------------*)
(** {3 Local formula conversion} *)

(** Converts and infers the type.
    Only the [set] part of the [SE.context] inside the environment
    is useful. 

    System expression optionally associated to each variable.
    If [v] is associated to [se], then [v] is a multi-term variable over
    [se]'s single systems. *)
val convert : 
  ?ty:Type.ty ->
  ?ty_env:Infer.env -> 
  ?pat:bool ->
  ?system_info:SE.t Mv.t ->
  conv_env -> 
  term ->
  Term.term * Type.ty

(*------------------------------------------------------------------*)
(** {3 Binders conversion} *)

(** Are variable tags supported during binder conversion *)
type bnds_tag_mode =
  | NoTags
  | DefaultTag of Vars.Tag.t

(** Convert binders. *)  
val convert_bnds : 
  ?ty_env:Infer.env -> 
  mode:bnds_tag_mode ->
  Env.t ->
  bnds ->
  Env.t * Vars.vars

val convert_bnds_tagged :
  ?ty_env:Infer.env -> 
  mode:bnds_tag_mode ->
  Env.t ->
  bnds_tagged ->
  Env.t * Vars.tagged_vars

(** Convert extended binders.
    Support binders with destruct, e.g. [(x,y) : bool * bool] *)
val convert_ext_bnds :
  ?ty_env:Infer.env -> 
  mode:bnds_tag_mode ->
  Env.t -> ext_bnds ->
  Env.t * Term.subst * Vars.vars

(*------------------------------------------------------------------*)
(** Convert a systeme expression variable binding *)
val convert_se_var_bnds :
  Env.t -> SE.p_bnds -> Env.t * SE.tagged_vars
              
(*------------------------------------------------------------------*)
(** {3 Global formulas conversion} *)

(** Converts and infers the type.
    Each part of the [SE.context] inside the environment
    is used when converting the corresponding kind of atom.
    
    [system_info] is allows to control variable usage in 
    mutli-terms (see [convert]). *)
val convert_global_formula : 
  ?ty_env:Infer.env -> 
  ?pat:bool ->
  ?system_info:SE.t Mv.t ->
  conv_env -> global_formula -> Equiv.form

val convert_any : conv_env -> any_term -> Equiv.any_form

(*------------------------------------------------------------------*)
(** {2 Misc} *)

val parse_projs : lsymb list option -> Projection.t list 

(*------------------------------------------------------------------*)
(** {2 Proof-terms} *)

type pt_cnt =
  | PT_symb     of Symbols.p_path * ty list option
  (** (path, optional type arguments) *)
  | PT_app      of pt_app
  | PT_localize of pt

(** a proof-term *)
and pt = pt_cnt L.located
    
(*------------------------------------------------------------------*)
(** proof term application *)
and pt_app = {
  pta_head : pt;
  pta_args : pt_app_arg list;
  pta_loc  : L.t;
}

(** proof term application argument *)
and pt_app_arg =
  | PTA_term of term
  | PTA_sub  of pt             (** sub proof-term *)
