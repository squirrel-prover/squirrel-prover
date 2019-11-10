(** Terms and facts used during parsing. *)

(** {2 Terms}
    It is required to have two different kind of terms. The one in this module
    is for parsing. Variables are identified by strings, instead of some
    variable type.Function symbols can be defined at runtime, and each new
    term typed checked. *)

type ord = Term.ord

type action_shape

type term =
  | Var of string
  | Taction of action_shape
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
  | Compare of ord*term*term

val pp_term : Format.formatter -> term -> unit

type fact = term Term.bformula

val pp_fact : Format.formatter -> fact -> unit

(** Terms may represent indices, messages or booleans *)
type kind = Index | Message | Boolean | Timestamp

(** {2 Declaration of new symbols}
  *
  * Hash function symbols are of kind message->message->message.
  * Asymmetric encryption function symbols are of kind
  * message->message->message->message.
  * Names are of kind index^n->message. Mutable cells are
  * similar but may contain messages or booleans. *)

exception Multiple_declarations

val declare_hash : string -> unit
val declare_aenc : string -> unit
val declare_name : string -> int -> unit
val declare_state : string -> int -> kind -> unit
val declare_abstract : string -> kind list -> kind -> unit
val declare_macro : string -> (string*kind) list -> kind -> term -> unit

(** {2 Term builders }
    Given a string [s] and a list of terms [l] build the term [s(l)]
  * according to what [s] refers to: if it is a declared primitive,
  * name or mutable cell, then its arity must be respected; otherwise
  * it is understood as a variable and [l] must be empty.
  * Raises [Type_error] if arities are not respected.
  * This function is intended for parsing, at a time where type
  * checking cannot be performed due to free variables. *)

val make_term : ?at_ts:term option -> string -> term list -> term
val make_action : (int * string list * int * string list) list -> action_shape
val make_pair : term -> term -> term

(** {2 Type-checking} *)

exception Type_error
type env = (string*kind) list
val check_term : env -> term -> kind -> unit
val check_state : string -> int -> kind
val check_fact : env -> fact -> unit

val is_hash : Term.fname -> bool

(** Populate theory with only builtin declarations *)
val initialize_symbols : unit -> unit

(** {2 Conversions}
    Convert terms inside the theory to to terms of the prover.
*)

type atsubst =
  | Term of string * Term.term
  | TS of string * Term.timestamp
  | Idx of string * Action.index

type tsubst = atsubst list

val pp_tsubst : Format.formatter -> tsubst -> unit

(** Convert to [Term.term], for local terms (i.e. with no timestamps). *)
val convert :
  Term.timestamp ->
  tsubst ->
  term ->
  Term.term

(** Convert to [Term.fact], for local terms (i.e. with no timestamps). *)
val convert_fact :
  Term.timestamp ->
  tsubst ->
  fact ->
  Term.fact

val convert_ts :
  tsubst ->
  term ->
  Term.timestamp

(** Convert to [Term.term], for global terms (i.e. with attached timestamps). *)
val convert_glob :
  tsubst ->
  term ->
  Term.term

(** Convert to [Term.constr], for global terms (i.e. with attached timestamps). *)
val convert_constr_glob :
  (string * kind) list ->
  tsubst ->
  fact ->
  Term.constr

(** Convert to [Term.fact], for global terms (i.e. with attached timestamps). *)
val convert_fact_glob :
  tsubst ->
  fact ->
  Term.fact

(** [convert_vars vars] Returns the timestamp and index variables substitution,
    in reverse order of declaration. By consequence, List.assoc properly handles
    the shadowing. *)
val convert_vars :
  (string * kind) list ->
  tsubst * Term.fvar list
