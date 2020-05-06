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
  * Although function symbols are known when a term is parsed, we use
  * here a very permissive [Fun] constructor which will be used to represent
  * both function applications and macros. *)
type kind = Sorts.esort

type term =
  | Var of string
  | Taction of string * term list
  | Tinit
  | Tpred of term
  | Diff of term*term
  | Seq of string list * term
  | ITE of term*term*term
  | Find of string list * term * term * term
  | Name of string * term list
  (** A name, whose arguments will always be indices. *)
  | Get of string * term option * term list
  (** [Get (s,ots,terms)] reads the contents of memory cell
    * [(s,terms)] where [terms] are evaluated as indices.
    * The second argument [ots] is for the optional timestamp at which the
    * memory read is performed. This is used for the terms appearing in
    * goals. *)
  | Fun of string * term list * term option
  (** Function symbol application,
    * where terms will be evaluated as indices or messages
    * depending on the type of the function symbol.
    * The third argument is for the optional timestamp. This is used for
    * the terms appearing in goals.*)
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

(** {2 Declaration of new symbols} *)


(** Declare a new function symbol of type message->message->message, * which
   satisfies PRF, and thus collision-resistance and EUF. *)
val declare_hash : ?index_arity:int -> string -> unit

(** Asymmetric encryption function symbols are defined by the triplet
    (enc,dec,pk).
    It satisfies CCA2. *)
val declare_aenc : string -> string -> string -> unit

(** Symmetric encryption function symbols are defined by the couple
    (enc,dec).
    It satisfies CCA2. *)
val declare_senc : string -> string -> unit


(** A signature is defined by a triplet, corresponding to (sign,checksign,pk).
   It satisfies EUF. *)
val declare_signature : string -> string -> string -> unit

(** [declare_name n i] declares a new name of type
  * [index^i -> message]. *)
val declare_name : string -> int -> unit

(** [declare_state n i s] declares a new state symbol of type
  * [index^i -> s] where [s] is either [boolean] or [message]. *)
val declare_state : string -> int -> Sorts.esort -> unit

(** [declare_abstract n i m] declares a new function symbol
  * of type [index^i -> message^m -> message]. *)
val declare_abstract : string -> index_arity:int -> message_arity:int -> unit

(** [declare_macro n [(x1,s1);...;(xn;sn)] s t] a macro symbol [s]
  * of type [s1->...->sn->s]
  * such that [s(t1,...,tn)] expands to [t[x1:=t1,...,xn:=tn]]. *)
val declare_macro :
  string -> (string*Sorts.esort) list -> Sorts.esort -> term -> unit

(** {2 Term builders }
    Given a string [s] and a list of terms [l] build the term [s(l)]
  * according to what [s] refers to: if it is a declared primitive,
  * name or mutable cell, then its arity must be respected; otherwise
  * it is understood as a variable and [l] must be empty.
  * Raises [Type_error] if arities are not respected.
  * This function is intended for parsing, at a time where type
  * checking cannot be performed due to free variables. *)

val make_term : ?at_ts:term -> string -> term list -> term
val make_pair : term -> term -> term

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

exception Conv of conversion_error

val pp_error : Format.formatter -> conversion_error -> unit

type env = (string*Sorts.esort) list

val check : ?local:bool -> env -> term -> Sorts.esort -> unit
val check_state : string -> int -> Sorts.esort

(* Returns true if the given function names corresponds to some associated
   checksign and pk functions, returns Some sign, where sign is the
   corresponding signature. Else, returnes None. *)

val check_signature : Term.fname -> Term.fname -> Term.fname option

(** {2 Conversions}
  * Convert terms inside the theory to terms of the prover. *)

val subst : term -> (string*term) list -> term

type esubst = ESubst : string * 'a Term.term -> esubst

type subst = esubst list

val subst_of_env : Vars.env -> subst

val parse_subst :
  Vars.env -> Vars.evar list -> term list -> Term.subst

val pp_subst : Format.formatter -> subst -> unit

val conv_index : subst -> term -> Vars.index

val convert :
  ?at:Term.timestamp ->
  subst ->
  term ->
  'a Sorts.sort ->
  'a Term.term
