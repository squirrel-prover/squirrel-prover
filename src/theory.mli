(** This module defines terms and facts used during parsing,
  * functions to type-check them, and convert them to proper
  * terms and formulas of the logic. *)

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

type lsymb = string Location.located

type term_i =
  | Tinit
  | Tpred of term
  | Diff  of term * term
  | Seq   of lsymb list * term
  | ITE   of term * term * term
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
  | ForAll  of (lsymb * Type.ety) list * term
  | Exists  of (lsymb * Type.ety) list * term
  | And  of term * term
  | Or   of term * term
  | Impl of term * term
  | Not  of term
  | True
  | False

and term = term_i Location.located

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
  ?index_arity:int -> ?in_ty:Type.ety -> ?out_ty:Type.ety ->
  lsymb ->
  Symbols.table

(** Asymmetric encryption function symbols are defined by the triplet
    (enc,dec,pk).
    It models an authenticated encryption. *)
val declare_aenc :
  Symbols.table ->
  ?ptxt_ty:Type.ety ->
  ?ctxt_ty:Type.ety ->
  ?rnd_ty:Type.ety ->
  ?sk_ty:Type.ety ->
  ?pk_ty:Type.ety ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It models an authenticated encryption. *)
val declare_senc :
  Symbols.table ->
  ?ptxt_ty:Type.ety ->
  ?ctxt_ty:Type.ety ->
  ?rnd_ty:Type.ety ->
  ?k_ty:Type.ety ->
  lsymb -> lsymb ->
  Symbols.table

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It models an authenticated encryption, jointly secure with hashes of the key.*)
val declare_senc_joint_with_hash :
  Symbols.table ->
  ?ptxt_ty:Type.ety ->
  ?ctxt_ty:Type.ety ->
  ?rnd_ty:Type.ety ->
  ?k_ty:Type.ety ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table

(** A signature is defined by a triplet, corresponding to (sign,checksign,pk).
    It satisfies EUF. *)
val declare_signature :
  Symbols.table ->
  ?m_ty:Type.ety ->
  ?sig_ty:Type.ety ->
  ?sk_ty:Type.ety ->
  ?pk_ty:Type.ety ->
  lsymb -> lsymb -> lsymb ->
  Symbols.table

(** [declare_name n i] declares a new name of type
  * [index^i -> message]. *)
val declare_name :
  Symbols.table -> lsymb -> int -> Symbols.table

(** [declare_state n [(x1,s1);...;(xn;sn)] s t] declares
    a new state symbol of type [s1->...->sn->s]
    where [si] is [index] and [s] is [message]
    such that value of [s(t1,...,tn)] for init timestamp
    expands to [t\[x1:=t1,...,xn:=tn\]]. *)
val declare_state :
  Symbols.table -> lsymb -> (lsymb * Type.ety) list -> Type.ety -> term
  -> Symbols.table
       
(** [get_init_states] returns all the initial values of declared state symbols,
    used to register the init action *)
val get_init_states :
  Symbols.table -> (Term.state * Term.message) list

(** [declare_abstract n i m] declares a new function symbol
  * of type [index^i -> message^m -> message]. *)
val declare_abstract :
  Symbols.table -> 
  index_arity:int ->
  ty_args:Type.univar list ->
  in_tys:Type.ety list ->
  out_ty:Type.ety ->
  lsymb ->
  Symbols.table

(** [declare_macro n [(x1,s1);...;(xn;sn)] s t] a macro symbol [s]
  * of type [s1->...->sn->s]
  * such that [s(t1,...,tn)] expands to [t\[x1:=t1,...,xn:=tn\]]. *)
val declare_macro :
  Symbols.table -> lsymb -> (string * Type.ety) list -> Type.ety -> term
  -> Symbols.table

(*------------------------------------------------------------------*)
(** {2 Term builders } *)

val empty : Location.t -> term

(** [var_i x] make a variable represented as [App (x,\[\])] *)
val var_i        : Location.t -> string -> term_i
val var          : Location.t -> string -> term
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
  | Untypable_equality   of term_i
  | String_expected      of term_i
  | Int_expected         of term_i
  | Tactic_type          of string
  | Index_not_var        of term_i
  | Assign_no_state      of string
  | BadNamespace         of string * Symbols.namespace
  | Freetyunivar
    
type conversion_error = Location.t * conversion_error_i

exception Conv of conversion_error

val pp_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> conversion_error -> unit

type env = (string * Type.ety) list

val check : Symbols.table -> ?local:bool -> env -> term -> Type.ety -> unit
val check_state : Symbols.table -> lsymb -> int -> Type.ety

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

val convert : conv_env -> subst -> term -> 'a Type.ty -> 'a Term.term

(** Existantial type wrapping a converted term and its sort.
    The location is the location of the original [Theory.term].  *)
type eterm = ETerm : 'a Type.ty * 'a Term.term * Location.t -> eterm

(** Convert a term to any sort (tries sequentially all conversions).
    Should return the most precise sort (i.e. [Boolean] before [Message]). *)
val econvert : conv_env -> subst -> term -> eterm option

(** [find_app_terms t names] returns the sublist of [names] for which there
  * exists a subterm [Theory.App(name,_)] or [Theory.AppAt(name,_,_)] in the
  * term [t]. *)
val find_app_terms : term -> string list -> string list
