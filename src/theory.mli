(** This module defines terms and facts used during parsing,
  * functions to type-check them, and convert them to proper
  * terms and formulas of the logic. *)

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
type kind = Sorts.esort


type term =
  | Tinit
  | Tpred of term
  | Diff of term*term
  | Seq of string list * term
  | ITE of term*term*term
  | Find of string list * term * term * term

  | App of string * term list 
  (** An application of a symbol to some arguments which as not been
    * disambiguated yet (it can be a name, a function symbol
    * application, a variable, ...)
    * [App(f,t1 :: ... :: tn)] is [f (t1, ..., tn)] *)

  | AppAt of string * term list * term 
  (** An application of a symbol to some arguments, at a given
    * timestamp.  As for [App _], the head function symbol has not been
    * disambiguated yet.
    * [AppAt(f,t1 :: ... :: tn,tau)] is [f (t1, ..., tn)\@tau] *)
                 
  | Compare of Atom.ord*term*term
  | Happens of term
  | ForAll of (string * kind) list * term
  | Exists of (string * kind) list * term
  | And of term * term
  | Or of term * term
  | Impl of term * term
  | Not of term
  | True
  | False

type formula = term

val pp : Format.formatter -> term -> unit

(** [var x] makes the variable [App (x,\[\])] *)
val var : string -> term

(** {2 Declaration of new symbols} *)


(** Declare a new function symbol of type message->message->message, * which
    satisfies PRF, and thus collision-resistance and EUF. *)
val declare_hash 
  : Symbols.table -> ?index_arity
                     :int -> string
  -> Symbols.table

(** Asymmetric encryption function symbols are defined by the triplet
    (enc,dec,pk).
    It models an authenticated encryption. *)
val declare_aenc 
  : Symbols.table -> string -> string -> string 
  -> Symbols.table

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It models an authenticated encryption. *)
val declare_senc 
  : Symbols.table -> string -> string
  -> Symbols.table

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It models an authenticated encryption, jointly secure with hashes of the key.*)
val declare_senc_joint_with_hash 
  : Symbols.table -> string -> string -> string
  -> Symbols.table

(** A signature is defined by a triplet, corresponding to (sign,checksign,pk).
    It satisfies EUF. *)
val declare_signature 
  : Symbols.table -> string -> string -> string 
  -> Symbols.table

(** [declare_name n i] declares a new name of type
  * [index^i -> message]. *)
val declare_name 
  : Symbols.table -> string -> int -> Symbols.table

(** [declare_state n i s] declares a new state symbol of type
  * [index^i -> s] where [s] is either [boolean] or [message]. *)
val declare_state 
  : Symbols.table -> string -> int -> Sorts.esort 
  -> Symbols.table

(** [declare_abstract n i m] declares a new function symbol
  * of type [index^i -> message^m -> message]. *)
val declare_abstract : 
  Symbols.table -> string -> index_arity:int -> message_arity:int 
  -> Symbols.table

(** [declare_macro n [(x1,s1);...;(xn;sn)] s t] a macro symbol [s]
  * of type [s1->...->sn->s]
  * such that [s(t1,...,tn)] expands to [t\[x1:=t1,...,xn:=tn\]]. *)
val declare_macro :
  Symbols.table -> string -> (string*Sorts.esort) list -> Sorts.esort -> term
  -> Symbols.table

(** {2 Term builders } *)

val empty : term

(** {2 Type-checking} *)

type conversion_error =
  | Arity_error of string*int*int
  | Untyped_symbol of string
  | Index_error of string*int*int
  | Undefined of string
  | Type_error of term * Sorts.esort
  | Timestamp_expected of term
  | Timestamp_unexpected of term
  | Untypable_equality of term
  | String_expected of term
  | Int_expected of term
  | Tactic_type of string
  | Index_not_var of term
  | Assign_no_state of string
  | StrictAliasError
  | BadNamespace of string * Symbols.namespace

exception Conv of conversion_error

val pp_error : Format.formatter -> conversion_error -> unit

type env = (string*Sorts.esort) list

val check : Symbols.table -> ?local:bool -> env -> term -> Sorts.esort -> unit
val check_state : Symbols.table -> string -> int -> Sorts.esort

(* Returns true if the given function names corresponds to some associated
   checksign and pk functions, returns Some sign, where sign is the
   corresponding signature. Else, returnes None. *)

val check_signature : Symbols.table -> Term.fname -> Term.fname -> Term.fname option

(** {2 Conversions}
  * Convert terms inside the theory to terms of the prover. *)

val subst : term -> (string*term) list -> term

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

val convert :
  conv_env ->
  subst ->
  term ->
  'a Sorts.sort ->
  'a Term.term

(** [find_app_terms t names] returns the sublist of [names] for which there
  * exists a subterm [Theory.App(name,_)] or [Theory.AppAt(name,_,_)] in the
  * term [t]. *)
val find_app_terms : term -> string list -> string list
