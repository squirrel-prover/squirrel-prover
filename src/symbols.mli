(** Symbols
  *
  * A notion of symbol with a global table of symbols, separated
  * into namespaces, and where each symbol is attached to a definition
  * whose type depends on the namespace. *)

(** Purely abstract type representing unknown namespace. *)
type unknown

(** ['a t] is the type of symbols of namespace ['a]. *)
type 'a t

(** Type of tables of persistent symbol definitions.
  * It is currently ineffective. *)
type table

(* Dummy table, for transition only. It will eventually disappear. *)
val dummy_table : table

(** Empty symbol table, for testing. *)
val empty_table : table

(** Symbol definitions *)

type kind = Sorts.esort

type function_def =
  | Hash
  | AEnc
  | Sign
  | CheckSign
  | PublicKey
  | Abstract of kind list * kind

type macro_def =
  | Input | Output | Cond | Exec | Frame
  | State of int * kind
    (** Macro that expands to the content of a state at a given
      * timestamp. *)
  | Global of int
    (** Global macros are used to encapsulate let-definitions.
      * They are indexed. *)
  | Local of kind list * kind
    (** Local macro definitions are explicitly defined by the
      * user, and may depend on arbitrary terms. *)

type channel
type name
type action
type fname
type macro

type _ def =
  | Channel : unit -> channel def
  | Name : int -> name def
  | Action : int -> action def
  | Function : (int * function_def) -> fname def
  | Macro : macro_def -> macro def

type some_def =
  | Exists : 'a def -> some_def
  | Reserved

(** Extensible type for data associated to symbols.
  * Due to circular dependencies, this is not type-safe, but
  * at least avoids having multiple hashtables for symbols. *)
type data = ..
type data += Empty
type data += AssociatedFunctions of (fname t) list

exception Multiple_declarations of string
exception Unbound_identifier of string
exception Incorrect_namespace

(** Converts a symbol to a string, for printing purposes. *)
val to_string : 'a t -> string

(** [def_of_string s] returns the definition of the symbol named [s].
  * @raise Unbound_identifier if no such symbol has been defined. *)
val def_of_string : string -> some_def

type wrapped = Wrapped : 'a t * 'a def -> wrapped
val of_string : string -> wrapped

(** Wrap a function into a new one which runs the previous one but
  * restores the table of symbols to its initial state before
  * terminating (either by returning a value or raising an exception).
  * This is mainly for testing purposes. *)
val run_restore : (unit -> unit) -> (unit -> unit)

(** Clear the symbol table, and restore all symbols declared with the builtin
    flag. *)
val restore_builtin : unit -> unit

(** Signature for namespaces *)
module type Namespace = sig

  (** Abstract type representing this namespace. *)
  type ns

  (** Type of values defining the symbols of this namespace. *)
  type def

  (** Reserve a fresh symbol name, resembling the given string. *)
  val reserve : table -> string -> table * ns t

  (** Define a symbol name that has been previously reserved
    * using [fresh]. *)
  val define : table -> ns t -> ?data:data -> def -> table

  (** Declare a new symbol, with a name resembling the given string,
    * defined by the given value. *)
  val declare :
    table -> string -> ?builtin:bool -> ?data:data -> def -> table * ns t

  (* Like declare, but use the exact string as symbol name.
   * @raise Multiple_declarations if the name is not available. *)
  val declare_exact :
    table -> string -> ?builtin:bool -> ?data:data -> def -> table * ns t

  (** [of_string s] returns [s] as a symbol, if it exists in this namespace.
    * @raise Unbound_identifier otherwise. *)
  val of_string : string -> ns t

  (** Get definition associated to some symbol. *)
  val get_def : ns t -> def

  (** [def_of_string s] is equivalent to [get_def (of_string s)]. *)
  val def_of_string : string -> def

  (** Get data associated to some symbol. *)
  val get_data : ns t -> data

  (** [data_of_string s] is equivalent to [get_data (of_string s)]. *)
  val data_of_string : string -> data

  (** Get definition and data at once. *)
  val get_all : ns t -> def * data

  (** Iter on the defined symbols of this namespace *)
  val iter : (ns t -> def -> data -> unit) -> unit

end

module Channel : Namespace with type def = unit with type ns = channel
module Name : Namespace with type def = int with type ns = name
module Action : Namespace with type def = int with type ns = action
module Function : Namespace
  with type def = int * function_def with type ns = fname
module Macro : Namespace with type def = macro_def with type ns = macro
