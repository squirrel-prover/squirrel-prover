(** Terms *)

type ord = Term.ord

(* TODO replace term list by string list when indices are expected ? *)
type term =
  | Var of string
  | Name of string * term list
  | Get  of string * term list
      (** [Get (s,terms)] reads the contents of memory cell
        * [(s,terms)] where [terms] are evaluated as indices. *)
  | Fun  of string * term list
      (** Function symbol application,
        * where terms will be evaluated as indices or messages
        * depending on the type of the function symbol. *)
  | Compare of ord*term*term

val pp_term : Format.formatter -> term -> unit

(** Facts *)

type fact = term Term.bformula

val pp_fact : Format.formatter -> fact -> unit

(** Terms may represent indices, messages or booleans *)

type kind = Index | Message | Boolean

(** Declaration of new symbols
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

(** Term builders *)

val make_term : string -> term list -> term
val make_pair : term -> term -> term

(** Type-checking *)

exception Type_error
type env = (string*kind) list
val check_term : env -> term -> kind -> unit
val check_state : string -> int -> kind
val check_fact : env -> fact -> unit

val is_hash : Term.fname -> bool

(** Populate theory with only builtin declarations *)
val initialize_symbols : unit -> unit

(** Convert to [Term.term]. *)
val convert :
  Action.action ->
  (string * Term.term) list ->
  (string * Action.index) list ->
  term ->
  Term.term

(** Convert to [Term.fact]. *)
val convert_fact :
  Action.action ->
  (string * Term.term) list ->
  (string * Action.index) list ->
  fact ->
  Term.fact
