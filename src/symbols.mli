(** This module defines a notion of symbol with a global table of symbols,
  * separated into namespaces, and where each symbol is attached to a
  * definition whose type depends on the namespace. *)

type lsymb = string Location.located

(*------------------------------------------------------------------*)
(** Type of a function symbol (Prefix or Infix)
    - infix symbols must start by a character in [infix_first_chars]
    - infix symbols must be without index parameters *)
type symb_type = [ `Prefix | `Infix ]

val infix_fist_chars : char list

(*------------------------------------------------------------------*)
(** ['a t] is the type of symbols of namespace ['a]. *)
type 'a t

val hash : 'a t -> int

(** Symbol groups:
  * symbols with the same name can exist in different groups.
  * Groups are usually called namespaces, but what we (improperly)
  * call namespaces here is different: it's more of a name kind. *)
type group

(** Type of tables of persistent symbol definitions.
  * It is currently ineffective. *)
type table

(** Associates a unique tag to a table. For memoisation. *)
val tag : table -> int

(** Each possible namespace is represented by an abstract datatype.
  * Their names are descriptive; [fname] is for function symbols. *)

(*------------------------------------------------------------------*)
type channel
type name
type action
type fname
type macro
type system
type process
type btype

(*------------------------------------------------------------------*)
type namespace =
  | NChannel
  | NName
  | NAction
  | NFunction
  | NMacro
  | NSystem
  | NProcess
  | NBType

val pp_namespace : Format.formatter -> namespace -> unit

val get_namespace : ?group:group -> table -> string -> namespace option

(*------------------------------------------------------------------*)
(** {2 Symbol definitions}
  *
  * Each symbol is defined by some data,
  * whose type depends on the namespace. *)

type function_def =
  | Hash
  | DDHgen
  | AEnc
  | ADec
  | SEnc
  | SDec
  | Sign
  | CheckSign
  | PublicKey
  | Abstract of symb_type

(** Indicates if a function symbol has been defined with
  * the specified definition. *)
val is_ftype : fname t -> function_def -> table -> bool

(*------------------------------------------------------------------*)
type bty_info = 
  | Ty_large
  | Ty_name_fixed_length

type bty_def = bty_info list

(*------------------------------------------------------------------*)
type name_def = { 
  n_iarr : int;                  (* index arity *)
  n_ty   : Type.message Type.ty; (* type *)
}

(*------------------------------------------------------------------*)
type macro_def =
  | Input | Output | Cond | Exec | Frame
  | State of int * Type.tmessage
    (** Macro that expands to the content of a state at a given
      * timestamp. *)
  | Global of int * Type.tmessage
    (** Global macros are used to encapsulate let-definitions.
      * They are indexed. *)

(*------------------------------------------------------------------*)
(** Information about symbol definitions, depending on the namespace.
  * Integers refer to the index arity of symbols. *)
type _ def =
  | Channel  : unit      -> channel def
  | Name     : name_def  -> name    def
  | Action   : int       -> action  def
  | Macro    : macro_def -> macro   def
  | System   : unit      -> system  def
  | Process  : unit      -> process def
  | BType    : bty_def   -> btype   def
        
  | Function : (Type.ftype * function_def) -> fname def
        
type edef =
  | Exists : 'a def -> edef
  | Reserved of namespace

(*------------------------------------------------------------------*)
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

(*------------------------------------------------------------------*)
(** {2 Basic namespace-independent operations} *)

(** Converts a symbol to a string, for printing purposes. *)
val to_string : 'a t -> string

(** Pretty-print a symbol. *)
val pp : Format.formatter -> 'a t -> unit

(** [def_of_lsymb s] returns the definition of the symbol named [s].
  * @raise Unbound_identifier if no such symbol has been defined. *)
val def_of_lsymb : ?group:group -> lsymb -> table -> edef

val is_defined : ?group:group -> string -> table -> bool

type wrapped = Wrapped : 'a t * 'a def -> wrapped

(** [of_lsymb s] returns the symbol associated to [s]
  * together with its defining data.
  * @raise Unbound_identifier if no such symbol has been defined. *)
val of_lsymb : ?group:group -> lsymb -> table -> wrapped

(** [of_lsymb_opt s] is the same as [of_lsymb_opt s], but return [None]
    if [s] is not defined. *)
val of_lsymb_opt : ?group:group -> lsymb -> table -> wrapped option

(*------------------------------------------------------------------*)
(** {2 Namespaces} *)

(** Signature for namespaces. *)
module type Namespace = sig

  (** Abstract type representing this namespace. *)
  type ns

  (** Type of values defining the symbols of this namespace. *)
  type def

  (** Reserve a fresh symbol name, resembling the given string. *)
  val reserve : table -> lsymb -> table * ns t

  (** Reserve a fresh symbol name. *)
  val reserve_exact : table -> lsymb -> table * ns t

  (** Define a symbol name that has been previously reserved
    * using [fresh]. *)
  val define : table -> ns t -> ?data:data -> def -> table

  (** Redefine a symbol name that has been previously defined. *)
  val redefine : table -> ns t -> ?data:data -> def -> table

  (** Declare a new symbol, with a name resembling the given string,
    * defined by the given value. *)
  val declare :
    table -> lsymb -> ?data:data -> def -> table * ns t

  (** Like declare, but use the exact string as symbol name.
    * @raise Multiple_declarations if the name is not available. *)
  val declare_exact :
    table -> lsymb -> ?data:data -> def -> table * ns t

  (** [of_lsymb s] returns [s] as a symbol, if it exists in this namespace.
    * @raise Unbound_identifier otherwise. *)
  val of_lsymb : lsymb -> table -> ns t

  (** [of_lsymb s] returns [Some s] as a symbol, if it exists in this
      namespace, and None otherwise. *)
  val of_lsymb_opt : lsymb -> table -> ns t option

  (** [cast_of_string s] always returns [s] as a symbol. *)
  val cast_of_string : string -> ns t

  (** Get definition and data at once. *)
  val get_all : ns t -> table -> def * data

  (** Get definition associated to some symbol. *)
  val get_def : ns t -> table -> def

  (** [def_of_lsymb s] is equivalent to [get_def (of_lsymb s)]. *)
  val def_of_lsymb : lsymb -> table -> def

  (** Get data associated to some symbol. *)
  val get_data : ns t -> table -> data

  (** [data_of_lsymb s] is equivalent to [get_data (of_lsymb s)]. *)
  val data_of_lsymb : lsymb -> table -> data

  (** Iterate on the defined symbols of this namespace. *)
  val iter : (ns t -> def -> data -> unit) -> table -> unit

  (** Fold over the defined symbols of this namespace. *)
  val fold : (ns t -> def -> data -> 'a -> 'a) -> 'a -> table -> 'a
end

module Channel  : Namespace with type def = unit    with type ns = channel
module BType    : Namespace with type def = bty_def with type ns = btype
module Action   : Namespace with type def = int     with type ns = action
module System   : Namespace with type def = unit    with type ns = system
module Process  : Namespace with type def = unit    with type ns = process

module Function : Namespace
  with type def = Type.ftype * function_def with type ns = fname

module Macro    : Namespace with type def = macro_def with type ns = macro
module Name     : Namespace with type def = name_def with type ns = name

(*------------------------------------------------------------------*)
(** {2 Error Handling} *)

type symb_err_i = 
  | Unbound_identifier    of string
  | Incorrect_namespace   of namespace * namespace (* expected, got *)
  | Multiple_declarations of string

type symb_err = Location.t * symb_err_i

val pp_symb_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> symb_err -> unit

exception SymbError of symb_err

(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

val get_bty_info   : table -> Type.tmessage -> bty_info list
val check_bty_info : table -> Type.tmessage -> bty_info -> bool

val is_infix     : fname t -> bool 
val is_infix_str : string  -> bool 

(*------------------------------------------------------------------*)
(** {2 Builtins} *)

val builtins_table : table

(** Returns the type of a builtin function *)
val ftype_builtin : fname t -> Type.ftype

(** Returns the type of a function *)
val ftype : table -> fname t -> Type.ftype

(*------------------------------------------------------------------*)
(** {3 Action builtins} *)

val init_action : action t

(** {3 Macro builtins} *)

val inp   : macro t
val out   : macro t
val cond  : macro t
val exec  : macro t
val frame : macro t

(** {3 Channel builtins} *)

val dummy_channel_lsymb : lsymb
val dummy_channel : channel t

(** {3 Function symbols builtins} *)

val fs_diff   : fname t

(** Boolean connectives *)

val fs_true   : fname t
val fs_false  : fname t
val fs_and    : fname t
val fs_or     : fname t
val fs_impl   : fname t
val fs_not    : fname t
val fs_ite    : fname t

(** Witness *)

val fs_witness : fname t

(** Successor over natural numbers *)

val fs_succ   : fname t

(** Adversary function *)

val fs_att    : fname t

(** Fail *)

val fs_fail   : fname t

(** Xor and its unit *)

val fs_xor    : fname t
val fs_zero   : fname t

(** Pairing *)

val fs_pair   : fname t
val fs_fst    : fname t
val fs_snd    : fname t

(** Boolean to Message *)
val fs_of_bool : fname t

(** Empty *)

val fs_empty  : fname t

(** Length *)

val fs_len    : fname t
val fs_zeroes : fname t

(*------------------------------------------------------------------*)
module Ss (S : Namespace) : Set.S with type elt := S.ns t 
module Ms (S : Namespace) : Map.S with type key := S.ns t 
