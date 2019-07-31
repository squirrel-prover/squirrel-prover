(** Terms *)

type ord = Term.ord

(* TODO replace term list by string list when indices are expected ? *)
type term =
  | Var of string
  | Taction of Action.action_shape
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

(** Facts *)

type fact = term Term.bformula

val pp_fact : Format.formatter -> fact -> unit

(** Terms may represent indices, messages or booleans *)

type kind = Index | Message | Boolean | Timestamp

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

val make_term : ?at_ts:term option -> string -> term list -> term
val make_action : (int * string list * int) list -> Action.action_shape
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

(** Convert to [Term.term], for local terms (i.e. with no timestamps). *)
val convert :
  Term.timestamp ->
  (string * Term.term) list ->
  (string * Action.index) list ->
  term ->
  Term.term

(** Convert to [Term.fact], for local terms (i.e. with no timestamps). *)
val convert_fact :
  Term.timestamp ->
  (string * Term.term) list ->
  (string * Action.index) list ->
  fact ->
  Term.fact

(** Convert to [Term.term], for global terms (i.e. with attached timestamps). *)
val convert_glob :
  (string * Term.timestamp) list ->
  (string * Action.index) list ->
  term ->
  Term.term

(** Convert to [Term.constr], for global terms (i.e. with attached timestamps). *)
val convert_constr_glob :
  (string * kind) list ->
  (string * Term.timestamp) list ->
  (string * Action.index) list ->
  fact ->
  Term.constr

(** Convert to [Term.fact], for global terms (i.e. with attached timestamps). *)
val convert_fact_glob :
  (string * Term.timestamp) list ->
  (string * Action.index) list ->
  fact ->
  Term.fact

(** [convert_vars vars] Returns the timestamp and index variables substitution,
    in reverse order of declaration. By consequence, List.assoc properly handles
    the shadowing. *)
val convert_vars :
  ('a * kind) list ->
  ('a * Term.tvar) list * ('a * Action.index) list
