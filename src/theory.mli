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

type term =
  | Var of string
  | Taction of string * term list
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

val pp_term : Format.formatter -> term -> unit

type fact = term Bformula.bformula

val pp_fact : Format.formatter -> fact -> unit

type formula = (term, (string * Sorts.esort) ) Formula.foformula

val formula_to_fact : formula -> fact

val formula_vars : formula -> (string * Sorts.esort) list

val pp_formula : Format.formatter -> formula -> unit

(** {2 Declaration of new symbols} *)


(** Declare a new function symbol of type message->message->message,
  * which satisfies PRF, and thus collision-resistance and EUF. *)
val declare_hash : string -> unit

(** Asymmetric encryption function symbols are of type
  * message->message->message->message. *)
val declare_aenc : string -> unit

(** [declare_name n i] declares a new name of type
  * [index^i -> message]. *)
val declare_name : string -> int -> unit

(** [declare_state n i s] declares a new name of type
  * [index^i -> s] where [s] is either [boolean] or [message]. *)
val declare_state : string -> int -> Sorts.esort -> unit

(** [declare_abstract n l s] declares a new function symbol
  * of type [l -> s]. *)
val declare_abstract : string -> Sorts.esort list -> Sorts.esort -> unit

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

exception Type_error

(** [Arity_error (s,i,j)] means that symbol [s] is used with
  * arity [i] when it actually has arity [j]. *)
exception Arity_error of string*int*int

type env = (string*Sorts.esort) list
val check_term : env -> term -> Sorts.esort -> unit
val check_state : string -> int -> Sorts.esort
val check_fact : env -> fact -> unit

val is_hash : Term.fname -> bool

(** {2 Conversions}
  * Convert terms inside the theory to terms of the prover. *)

val subst : term -> (string*term) list -> term
val subst_fact : fact -> (string*term) list -> fact

type esubst = ESubst : string * 'a Term.term -> esubst

type subst = esubst list

val subst_of_env : Vars.env -> subst

val parse_subst :
  Vars.env -> Vars.evar list -> term list -> Term.subst


val pp_subst : Format.formatter -> subst -> unit

val conv_index : subst -> term -> Vars.index

(** Convert to [Term.term], for local terms (i.e. with no timestamps). *)
val convert :
  Term.timestamp ->
  subst ->
  term ->
  Term.message

(** Convert to [Term.fact], for local terms (i.e. with no timestamps). *)
val convert_fact :
  Term.timestamp ->
  subst ->
  fact ->
  Bformula.fact

val convert_ts :
  subst ->
  term ->
  Term.timestamp

(** Convert to [Term.term], for global terms (i.e. with attached timestamps). *)
val convert_glob :
  subst ->
  term ->
  Term.message

(** Convert to [Formula.formula], for local terms (i.e. with no timestamps). *)
val convert_formula :
  env ->
  Term.timestamp ->
  subst ->
  formula ->
  Formula.formula

(** Convert [fact] to [Bformula.fact],
  * for global terms (i.e. with attached timestamps). *)
val convert_fact_glob :
  subst ->
  fact ->
  Bformula.fact

(** Convert to [formula] to [Formula.formula],
  * for global terms (i.e. with attached timestamps).
  * Requires a typing environment. *)
val convert_formula_glob :
  env ->
  subst ->
  formula ->
  Formula.formula

(** [convert_vars vars] Returns the timestamp and index variables substitution,
    in reverse order of declaration. By consequence, List.assoc properly handles
    the shadowing. *)
val convert_vars :
  Vars.env ref ->
  env ->
  subst * Vars.evar list
