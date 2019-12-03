(** Symbols
  *
  * A notion of symbol with a global table of symbols, separated
  * into namespaces, and where each symbol is attached to a definition
  * whose type depends on the namespace. *)

(** ['a t] is the type of symbols of namespace ['a]. *)
type 'a t

exception Multiple_declarations
exception Unbound_identifier
exception Incorrect_namespace

(** Converts a symbol to a string, for printing purposes. *)
val to_string : 'a t -> string

(** Indicates whether a symbol of that name has been declared. *)
val exists : string -> bool

(** The type of definitions attached to symbols.
  * It is extensible, with one case for each namespace. *)
type def = ..

(** Get the definition of a symbol. This should be used when the namespace
  * of the symbol is not known precisely. Otherwise, one should rather use
  * the more precise namespace-specific functionality. *)
val get_def : 'a t -> def

(** Purely abstract type for symbols of unknown namespace. *)
type unknown

(** Get the symbol associated to a string.
  * @raise Unbound_identifier is no symbol of that name has been declared. *)
val of_string : string -> unknown t

(** [def_of_string s] is equivalent to [get_def (of_string s)]. *)
val def_of_string : string -> def

(** Wrap a function into a new one which runs the previous one but
  * restores the table of symbols to its initial state before
  * terminating (either by returning a value or raising an exception).
  * This is mainly for testing purposes. *)
val run_restore : (unit -> unit) -> (unit -> unit)

(** Signature for namespaces *)
module type Namespace = sig

  (** Type of data carried by symbols in this namespace *)
  type data

  (** Constructor for definitions of this namespace *)
  type def += C of data

  (** Abstract type representing this namespace *)
  type ns

  (** Reserve a fresh symbol name, resembling the given string. *)
  val reserve : string -> ns t

  (** Define a symbol name that has been previously reserved
    * using [fresh]. *)
  val define : ns t -> data -> unit

  (** Declare a new symbol, with a name resembling the given string,
    * defined by the given value. *)
  val declare : string -> data -> ns t

  (* Like declare, but use the exact string as symbol name.
   * @raise Multiple_declarations if the name is not available. *)
  val declare_exact : string -> data -> ns t

  (** [of_string s] returns [s] as a symbol, if it exists in this namespace.
    * @raise Unbound_identifier otherwise. *)
  val of_string : string -> ns t

  (** Get the definition of a symbol in this namespace. *)
  val get_def : ns t -> data

  (** [def_of_string s] is equivalent to [get_def (of_string s)]. *)
  val def_of_string : string -> data

  (** Iter on the defined symbols of this namespace *)
  val iter : (ns t -> data -> unit) -> unit

end

module type S = sig
  type data
end

(** Create a new namespace
  * where symbols are defined by values of type [M.data]. *)
module Make (M:S) : Namespace with type data = M.data
