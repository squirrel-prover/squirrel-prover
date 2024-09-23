(** This module defines a notion of symbol with a global table of
    symbols.
    Each symbol has a symbol kind (e.g. an operator and a channel
    have different kinds), and each symbol is attached to a
    definition whose Ocaml type depends on the kind. *)

open Utils

module L = Location

(*------------------------------------------------------------------*)
(** A parsed symbol *)
type lsymb = string L.located

(** A parsed namespace path *)
type p_npath = string L.located list

(** A parsed symbol path *)
type p_path = p_npath * string L.located

val p_npath_loc : p_npath -> L.t
val p_path_loc  : p_path  -> L.t

val p_npath_to_string : ?sep:string -> p_npath -> string
val p_path_to_string  : ?sep:string -> p_path  -> string

(*------------------------------------------------------------------*)
(** An untyped namespace path. Unsafe API. *)
type s_npath = string list

(** An untyped symbol path [(p,s)] representing [p.s]. Unsafe API. *)
type s_path = string list * string

val s_npath_to_string : ?sep:string -> s_npath -> string
val s_path_to_string  : ?sep:string -> s_path  -> string

(*------------------------------------------------------------------*)
(** Type of a function symbol (Prefix or Infix)
    - infix symbols must start by an allowed character (see the lexer)
    - infix symbols must be without index parameters *)

type assoc = [`Right | `Left | `NonAssoc]
type symb_type = [ `Prefix | `Infix of assoc ]

(*------------------------------------------------------------------*)
type symbol_kind =
  | Channel
  | Config
  | Oracle
  | Name
  | Action
  | Operator   (** abtract and concrete operators *)
  | Macro
  | System
  | Process
  | BType      (** type declarations *)
  | Game
  | HintDB
  | Lemma
  | Predicate
  | Import
  | Namespace

val pp_symbol_kind : symbol_kind formatter

(*------------------------------------------------------------------*)
(** {3 Symbols} *)

(*------------------------------------------------------------------*)
(** Symbol kind groups:
    symbols with the same name can exist in different symbol kind
    groups. *)
type group

val group_to_string : group -> string

(*------------------------------------------------------------------*)
(** ['a t] is the type of symbols of kind ['a]. *)
type 'a t

val hash : 'a t -> int

(** Converts a symbol to a string, for printing purposes. *)
val to_string : 'a t -> string

(** Pretty-print a symbol. *)
val pp : 'a t formatter

(*------------------------------------------------------------------*)
(** Each possible symbol kind is represented by an abstract datatype.
    Their names are descriptive; [fname] is for function symbols. *)

type _channel
type _config
type _oracle
type _name
type _action
type _fname
type _macro
type _system
type _process
type _btype
type _game
type _hintdb
type _lemma
type _predicate
type _import
type _namespace


(*------------------------------------------------------------------*)
(** {3 Paths} *)

(** A namespace path is simply a list of namespaces *)
type npath = private {
  npath : _namespace t list;
  id    : int;                    (** for hash-consing *)
}

(** A path to a symbol of kind ['a].
    [{np; s}] represents the path [np.s]. *)
type 'a path = private {
  np : npath;
  s  : 'a t;
  id : int;                    (** for hash-consing *)
}

(*------------------------------------------------------------------*)
type channel   = _channel   path
type config    = _config    path
type oracle    = _oracle    path
type name      = _name      path
type action    = _action    path
type fname     = _fname     path
type macro     = _macro     path
type system    = _system    path
type process   = _process   path
type btype     = _btype     path
type game      = _game      path
type hintdb    = _hintdb    path
type lemma     = _lemma     path
type predicate = _predicate path
type import    = _import    path
type namespace = _namespace path

(*------------------------------------------------------------------*)
val pp_npath : npath   formatter
val pp_path  : 'a path formatter

(*------------------------------------------------------------------*)
val npath_to_string : ?sep:string -> npath   -> string
val path_to_string  : ?sep:string -> 'a path -> string

(*------------------------------------------------------------------*)
val npath_id : npath   -> int     (** unique *)
val path_id  : 'a path -> int     (** unique *)

(*------------------------------------------------------------------*)
val npath_equal : npath   ->   npath -> bool
val path_equal  : 'a path -> 'a path -> bool

(*------------------------------------------------------------------*)
(** Build a namespace path (with hash-consing) *)
val npath : _namespace t list -> npath

(** Extends a namespace *)
val npath_app : npath -> _namespace t list -> npath

(** Build a namespace path from a [s_npath]. Unsafe API. *)
val of_s_npath : s_npath -> npath

val top_npath : npath

(*------------------------------------------------------------------*)
(** Build a path (with hash-consing) *)
val path : npath -> 'a t -> 'a path


(*------------------------------------------------------------------*)
(** In addition to their definition data, some more data can be attached
    to symbols. This is used for data that is defined in modules that
    depend on this module, through an extensible datatype.
    Due to circular dependencies, this is not type-safe. *)
type data = ..
type data += Empty

(*------------------------------------------------------------------*)
(** A symbol table mapping symbol paths to their definition (=
    [status] + [data]). *)
type table

(** For debugging *)
val pp_table : table formatter

(** Associates a unique tag to a table. For memoisation. *)
val tag : table -> int

(*------------------------------------------------------------------*)
(** Return the current scope *)
val scope : table -> npath

(*------------------------------------------------------------------*)
(** Convert a surface npath to a npath. *)
val convert_npath : p_npath -> table -> npath

(*------------------------------------------------------------------*)
(** {2 Symbol kinds} *)

(** Signature a new kind of symbols. *)
module type SymbolKind = sig

  (** Abstract type representing this kind. *)
  type ns

  val remove : ns path -> table -> table

  (** Reserve a fresh symbol name in the current namespace. *)
  val reserve : approx:bool -> table -> lsymb -> table * ns path

  (** Define a symbol name that has been previously reserved
      using [fresh]. *)
  val define : table -> ?data:data -> ns path -> table

  (** Redefine a symbol name that has been previously defined. *)
  val redefine : table -> ?data:data -> ns path -> table

  (** Declare a new symbol in the namespace [scope] (default to the
      current namespace [scope table]).
      @raise Multiple_declarations if the name is not available
      and [not approx] holds. *)
  val declare :
    approx:bool -> table -> ?scope:npath -> ?data:data -> lsymb -> table * ns path

  val is_reserved : ns path -> table -> bool

  (** Get data associated to some symbol.
      Always succeed for paths constructed through the type-safe API.
      @raise Not_found if the path (built from the unsafe API) does
      not map to anything. *)
  val get_data : ns path -> table -> data

  (*------------------------------------------------------------------*)
  (** [mem_sp p table] checks if [p] exists for this kind in [table]. *)
  val mem_sp : s_path -> table -> bool

  (** [mem_sp top s table] checks if [top.s] exists for this kind in [table]. *)
  val mem_s : npath -> string -> table -> bool

  (** [mem_p p table] checks if [p] exists for this kind in [table]. *)
  val mem_p : p_path -> table -> bool

  (*------------------------------------------------------------------*)
  (** Build a symbol path from a [s_path]. Unsafe API. *)
  val of_s_path : s_path -> ns path

  (** Build a symbol path from a [npath] and a string. Unsafe API. *)
  val of_string : npath -> string -> ns path

  (*------------------------------------------------------------------*)
  (** {3 Typing and conversion} *)

  (*------------------------------------------------------------------*)
  (** Convert a surface language path (qualified or short) to a path and
      retrieve the associated data. *)

  (** Return a single match. *)
  val convert1 : p_path -> table -> ns path * data

  (** Return all matches.
      Result list cannot be empty, except if [allow_empty] is true. *)
  val convert : ?allow_empty:bool -> p_path -> table -> (ns path * data) list

  (** Get only the path (and ignore additional matches if any). *)
  val convert_path : p_path -> table -> ns path

  (*------------------------------------------------------------------*)
  (** {3 Iterators} *)

  (** Iterate on the defined symbols of this kind. *)
  val iter : (ns path -> data -> unit    )       -> table -> unit

  (** Fold over the defined symbols of this kind. *)
  val fold : (ns path -> data -> 'a -> 'a) -> 'a -> table -> 'a

  (** Map over the defined symbols of this kind. *)
  val map : (ns path -> data -> data    )        -> table -> table
end

(*------------------------------------------------------------------*)
module Config    : SymbolKind with type ns = _config
module Oracle    : SymbolKind with type ns = _oracle
module Channel   : SymbolKind with type ns = _channel
module BType     : SymbolKind with type ns = _btype
module Game      : SymbolKind with type ns = _game
module Action    : SymbolKind with type ns = _action
module System    : SymbolKind with type ns = _system
module Process   : SymbolKind with type ns = _process
module HintDB    : SymbolKind with type ns = _hintdb
module Lemma     : SymbolKind with type ns = _lemma
module Import    : SymbolKind with type ns = _import
module Predicate : SymbolKind with type ns = _predicate
module Operator  : SymbolKind with type ns = _fname
module Macro     : SymbolKind with type ns = _macro
module Name      : SymbolKind with type ns = _name
module Namespace : SymbolKind with type ns = _namespace

(*------------------------------------------------------------------*)
(** {2 Namespaces} *)

(** Enter some namespaces (command [namespace N1. ... .NL]) *)
val namespace_enter : table -> p_npath -> table

(** Exit some namespaces (command [exit N1. ... .NL]) *)
val namespace_exit : table -> p_npath -> table

(** Open a namespace, bringing its definitions in scope
    (command [open N1. ... .NL]) *)
val namespace_open : table -> npath -> table

(** Close a namespace, removing its definitions from scope
    (command [close N1. ... .NL]) *)
val namespace_close : table -> npath -> table

(*------------------------------------------------------------------*)
(** {2 Error Handling} *)

type error_i =
  | Unbound_identifier    of group * string option * string
  (** [string] unknown in optional namespace [npath] *)
  | Incorrect_kind        of symbol_kind * symbol_kind (** expected, got *)
  | Multiple_declarations of npath * string * symbol_kind * group
  | Failure of string

type error = L.t * error_i

val pp_error :
  (Format.formatter -> L.t -> unit) ->
  Format.formatter -> error -> unit

exception Error of error

(*------------------------------------------------------------------*)
(** {2 Sets and maps} *)

module Sp (S : SymbolKind) : Set.S with type elt := S.ns path
module Mp (S : SymbolKind) : Map.S with type key := S.ns path

(*------------------------------------------------------------------*)
(** {2 Some data definitions}

    Each symbol is defined by some data,
    whose type depends on the kind. *)

(*------------------------------------------------------------------*)
(** {3 Data definitions for operators (abstract and concrete)}

    Contain the data definitions for concrete and abstract operators,
    except for some fields of concrete operators that are postponed
    after the definition of terms. *)

module OpData : sig

  (*------------------------------------------------------------------*)
  (** Different variants on the Diffie-Hellman crypto assumption *)
  type dh_hyp =
    | DH_DDH
    | DH_CDH
    | DH_GDH

  (** Definition on an abstract operator *)
  type abstract_def =
    | Hash
    | DHgen of dh_hyp list
    | AEnc
    | ADec
    | SEnc
    | SDec
    | Sign
    | CheckSign
    | PublicKey
    | Abstract of symb_type

  type associated_fun = fname list

  (*------------------------------------------------------------------*)
  (** Extensible type for concrete operators:
      see to [operator.ml] for the single constructor of [concrete_def].
      (the type is postponed because its definition uses terms,
      which are defined after the [Symbols] module).  *)
  type concrete_def = ..

  (*------------------------------------------------------------------*)
  type def =
    | Abstract of abstract_def * associated_fun
    | Concrete of concrete_def

  type op_data = {
    ftype : Type.ftype;
    def   : def;
  }

  type data += Operator of op_data

  (*------------------------------------------------------------------*)
  val pp_abstract_def : abstract_def formatter

  (** Pretty-printer for function names (properly parenthesized infix
      symbols) *)
  val pp_fname : fname formatter

  (*------------------------------------------------------------------*)
  val as_op_data : data -> op_data

  val get_data : fname -> table -> op_data

  val get_abstract_data : fname -> table -> abstract_def * associated_fun

  val ftype : table -> fname -> Type.ftype

  (*------------------------------------------------------------------*)
  val is_abstract : fname -> table -> bool

  (** Indicates if an abstract function symbol has been defined with
      the specified definition. *)
  val is_abstract_with_ftype : fname -> abstract_def -> table -> bool
end

(*------------------------------------------------------------------*)
(** {3 Macro data}  *)

(* FIXME: quantum: cleanup *)
(** Extensible type for general, global and state macros:
    - see [macros.ml] for [global_macro_def].
    - see [macros.ml] for [general_macro_def].
    - see [theory.ml] for [state_macro_def].

    (the types are postponed because their definition uses terms,
    which are defined after the [Symbols] module).  *)
type general_macro_def = ..
type global_macro_def = ..
type state_macro_def = ..

type macro_data =
  | General of general_macro_def
  (** General macro definition. *)
  | State  of int * Type.ty * state_macro_def
  (** Stateful cells. *)
  | Global of int * Type.ty * global_macro_def
  (** Global macros are used to encapsulate let-definitions. *)

type data += Macro of macro_data

exception Macro_reserved_no_def

(** Raise [Macro_reserved_no_def] if the macro is registered but not
    yet defined. *)
val as_macro_data  : data -> macro_data
val get_macro_data : macro -> table -> macro_data

(*------------------------------------------------------------------*)
(** {3 Name data} *)

type name_data = {
  n_fty : Type.ftype; (** restricted to: (Index | Timestamp)^* -> ty *)
}

type data += Name of name_data

val as_name_data : data -> name_data
val get_name_data : name -> table -> name_data

(*------------------------------------------------------------------*)
(** {3 Type information: Ocaml type declaration}  *)

module TyInfo : sig
  (** Type information associated to base types.
      Restrict the instantiation domain of a type. *)
  type t =
    | Large               (** collision probabiliy between names is negligible *)
    | Name_fixed_length   (** for any η, all names have the same length *)
    | Finite              (** finite for all η *)
    | Fixed               (** independent from η *)
    | Well_founded        (** well-founded for all η *)
    | Enum                (** enumerable in poly time  *)
    | Serializable        (** bit-string encodable *)

  type data += Type of t list

  (*------------------------------------------------------------------*)
  val parse : lsymb -> t

  (*------------------------------------------------------------------*)
  val get_data : btype -> table -> t list

  (*------------------------------------------------------------------*)
  val get_bty_infos  : table -> Type.ty -> t list
  val check_bty_info : table -> Type.ty -> t -> bool

  (*------------------------------------------------------------------*)
  (** Is the type a finite type, e.g. [Index] and [Timestamp] *)
  val is_finite : table -> Type.ty -> bool

  (** Is the type a fixed set (independent from the security
      parameter η.
      (e.g. [Index], [Timestamp] and [Message]) *)
  val is_fixed : table -> Type.ty -> bool

  (** The serializability order of the term. E.g. 
      - [message] is serializable as a bit-string (obviously), 
         and is thus order 0. 
      - [message -> message]              is order 1. 
      - [message -> message -> message]   is order 1.
      - [(message -> message) -> message] is order 2. 
      Returns [None] if no order could be inferred (e.g. because there
      are type variables). *)
  val serializability_order : table -> Type.ty -> int option
    
  (** Is the type enumerable in polynomial time. *)
  val is_enum : table -> Type.ty -> bool

  (** Are the names all of the same length. *)
  val is_name_fixed_length : table -> Type.ty -> bool

  (** Is the type well-founded for [Term.mk_lt], e.g. [Index], [Timestamp]
      or [Message]. *)
  val is_well_founded : table -> Type.ty -> bool
end

(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

val is_infix     : fname -> bool
val is_infix_str : string  -> bool

val infix_assoc : fname -> assoc

(*------------------------------------------------------------------*)
val is_infix_predicate : predicate -> bool
val infix_assoc_predicate : predicate -> assoc

(*------------------------------------------------------------------*)
(** {2 Builtins} *)

(** symbols table after processing the prelude *)
val builtins_table : unit -> table

(** Returns the type of a builtin function *)
val ftype_builtin : fname -> Type.ftype

(** Set the symbols table after processing the prelude.
    **Only use once in the toplevel prover.** *)
val set_builtins_table_after_processing_prelude : table -> unit

(*------------------------------------------------------------------*)
(** {3 Action builtins} *)

val init_action : action

(*------------------------------------------------------------------*)
(** {3 Macro builtins} *)

(*------------------------------------------------------------------*)
(** Macros for the classical execution model *)
val inp   : macro
val out   : macro
val cond  : macro
val exec  : macro
val frame : macro

(*------------------------------------------------------------------*)
(** Namepath for the quantum execution model *)
val quant_npath : npath

(** Macros for the quantum execution model *)
val q_inp   : macro
val q_out   : macro
val q_state : macro
val q_cond  : macro
val q_exec  : macro
val q_frame : macro

val is_quantum_macro : macro -> bool

(*------------------------------------------------------------------*)
(** {3 Channel builtins} *)

val dummy_channel_lsymb : lsymb
val dummy_channel : channel

(*------------------------------------------------------------------*)
(** {3 Abstract operator symbols builtins} *)

val fs_diff : fname

(** Happens *)

val fs_happens : fname

(** Pred *)

val fs_pred : fname

(** Boolean connectives *)

val fs_true  : fname
val fs_false : fname
val fs_and   : fname
val fs_or    : fname
val fs_impl  : fname
val fs_iff   : fname
val fs_not   : fname
val fs_ite   : fname

(** Comparison *)
val fs_eq  : fname
val fs_neq : fname
val fs_leq : fname
val fs_lt  : fname
val fs_geq : fname
val fs_gt  : fname

(** Successor over natural numbers *)

val fs_succ : fname

(** Adversary function *)

val fs_att  : fname              (** classical attacker *)
val fs_qatt : fname              (** quantum attacker *)

(** Fail *)

val fs_fail : fname

(** Xor and its unit *)

val fs_xor  : fname
val fs_zero : fname

(** Pairing *)

val fs_pair : fname
val fs_fst  : fname
val fs_snd  : fname

(** Boolean to Message *)
val fs_of_bool : fname

(** Empty *)

val fs_empty  : fname

(** Length *)

val fs_len    : fname
