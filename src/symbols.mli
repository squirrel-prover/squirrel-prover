(** This module defines a notion of symbol with a global table of symbols,
  * separated into namespaces, and where each symbol is attached to a
  * definition whose type depends on the namespace. *)

(** ['a t] is the type of symbols of namespace ['a]. *)
type 'a t

(** Type of tables of persistent symbol definitions.
  * It is currently ineffective. *)
type table

(* Dummy table, for transition only. It will eventually disappear. *)
val dummy_table : table

(** Empty symbol table, for testing. *)
val empty_table : table

(** Each possible namespace is represented by an abstract datatype.
  * Their names are descriptive; [fname] is for function symbols. *)

type channel
type name
type action
type fname
type macro

(** {2 Symbol definitions}
  *
  * Each symbol is defined by some data,
  * whose type depends on the namespace. *)

type function_def =
  | Hash
  | AEnc
  | ADec
  | SEnc
  | SDec
  | Sign
  | CheckSign
  | PublicKey
  | Abstract of int (** Message arity *)

(** Indicates if a function symbol has been defined with
  * the specified definition. *)
val is_ftype : fname t -> function_def -> bool

type macro_def =
  | Input | Output | Cond | Exec | Frame
  | State of int * Sorts.esort
    (** Macro that expands to the content of a state at a given
      * timestamp. *)
  | Global of int
    (** Global macros are used to encapsulate let-definitions.
      * They are indexed. *)
  | Local of Sorts.esort list * Sorts.esort
    (** Local macro definitions are explicitly defined by the
      * user, and may depend on arbitrary terms. *)

(** Information about symbol definitions, depending on the namespace.
  * Integers refer to the index arity of symbols. *)
type _ def =
  | Channel : unit -> channel def
  | Name : int -> name def
  | Action : int -> action def
  | Function : (int * function_def) -> fname def
  | Macro : macro_def -> macro def

type edef =
  | Exists : 'a def -> edef
  | Reserved

(** {2 Data}
  * In addition to their definition data, some more data can be attached
  * to symbols. This is used for data that is defined in modules that
  * depend on this module, through an extensible datatype. *)

(** Extensible type for data associated to symbols.
  * Due to circular dependencies, this is not type-safe, but
  * at least avoids having multiple hashtables for symbols. *)
type data = ..
type data += Empty
type data += AssociatedFunctions of (fname t) list

(** {2 Basic namespace-independent operations} *)

exception Multiple_declarations of string
exception Unbound_identifier of string
exception Incorrect_namespace

(** Converts a symbol to a string, for printing purposes. *)
val to_string : 'a t -> string

(** [def_of_string s] returns the definition of the symbol named [s].
  * @raise Unbound_identifier if no such symbol has been defined. *)
val def_of_string : string -> edef

type wrapped = Wrapped : 'a t * 'a def -> wrapped

(** [of_string s] returns the symbol associated to [s]
  * together with its defining data.
  * @raise Unbound_identifier if no such symbol has been defined. *)
val of_string : string -> wrapped

(** {2 Testing utilities} *)

(** Wrap a function into a new one which runs the previous one but
  * restores the table of symbols to its initial state before
  * terminating (either by returning a value or raising an exception).
  * This is mainly for testing purposes. *)
val run_restore : (unit -> unit) -> (unit -> unit)

(** Clear the symbol table, and restore all symbols declared with the builtin
    flag. *)
val restore_builtin : unit -> unit

(** {2 Namespaces} *)

(** Signature for namespaces. *)
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

  (** Like declare, but use the exact string as symbol name.
    * @raise Multiple_declarations if the name is not available. *)
  val declare_exact :
    table -> string -> ?builtin:bool -> ?data:data -> def -> table * ns t

  (** [of_string s] returns [s] as a symbol, if it exists in this namespace.
    * @raise Unbound_identifier otherwise. *)
  val of_string : string -> ns t

  (** [cast_of_string s] always returns [s] as a symbol. *)
  val cast_of_string : string -> ns t

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

  (** Iterate on the defined symbols of this namespace. *)
  val iter : (ns t -> def -> data -> unit) -> unit

  (** Fold over the defined symbols of this namespace. *)
  val fold : (ns t -> def -> data -> 'a -> 'a) -> 'a -> 'a
end

module Channel : Namespace with type def = unit with type ns = channel
module Name : Namespace with type def = int with type ns = name
module Action : Namespace with type def = int with type ns = action
module Function : Namespace
  with type def = int * function_def with type ns = fname

module Macro : Namespace with type def = macro_def with type ns = macro
