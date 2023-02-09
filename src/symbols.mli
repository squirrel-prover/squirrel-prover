(** This module defines a notion of symbol with a global table of symbols,
    separated into namespaces, and where each symbol is attached to a
    definition whose type depends on the namespace. *)

type lsymb = string Location.located

(*------------------------------------------------------------------*)
(** Type of a function symbol (Prefix or Infix)
    - infix symbols must start by a character in [infix_first_chars]
    - infix symbols must be without index parameters *)

type assoc = [`Right | `Left | `NonAssoc]
type symb_type = [ `Prefix | `Infix of assoc ]

val infix_fist_chars : char list

(*------------------------------------------------------------------*)
(** ['a t] is the type of symbols of namespace ['a]. *)
type 'a t

val hash : 'a t -> int

(** Symbol groups:
    symbols with the same name can exist in different groups.
    Groups are usually called namespaces, but what we (improperly)
    call namespaces here is different: it's more of a name kind. *)
type group

(** Type of tables of persistent symbol definitions.
    It is currently ineffective. *)
type table

(** Associates a unique tag to a table. For memoisation. *)
val tag : table -> int

(** Each possible namespace is represented by an abstract datatype.
    Their names are descriptive; [fname] is for function symbols. *)

(*------------------------------------------------------------------*)
type _channel
type _config
type _name
type _action
type _fname
type _macro
type _system
type _process
type _btype
type _hintdb
type _lemma
  
type channel = _channel t
type config  = _config  t
type name    = _name    t
type action  = _action  t
type fname   = _fname   t
type macro   = _macro   t
type system  = _system  t
type process = _process t
type btype   = _btype   t
type hintdb  = _hintdb  t
type lemma   = _lemma   t
    
(*------------------------------------------------------------------*)
type namespace =
  | NChannel
  | NConfig
  | NName
  | NAction
  | NFunction
  | NMacro
  | NSystem
  | NProcess
  | NBType      (** type declarations *)
  | NHintDB
  | NLemma
    
val pp_namespace : Format.formatter -> namespace -> unit

val get_namespace : ?group:group -> table -> string -> namespace option

(*------------------------------------------------------------------*)
(** {2 Symbol definitions}

    Each symbol is defined by some data,
    whose type depends on the namespace. *)

(*------------------------------------------------------------------*)
(** Different variants on the Diffie-Hellman crypto assumption      *)
                          
type dh_hyp =
  | DH_DDH
  | DH_CDH
  | DH_GDH

type function_def =
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
  | Operator                    (* definition in associated data *)

(** Indicates if a function symbol has been defined with
    the specified definition. *)
val is_ftype : fname -> function_def -> table -> bool

(*------------------------------------------------------------------*)
(** {2 Type information: Ocaml type declaration}  *)

(** Type information associated to base types. 
    Restrict the instantiation domain of a type. *)
type bty_info =
  | Large               (** collision probabiliy between names is negligible *)
  | Name_fixed_length   (** for any η, all names have the same length *)
  | Finite              (** finite for all η *)
  | Fix                 (** independent from η *)
  | Well_founded        (** well-founded for all η *)
    
type bty_infos = bty_info list

(*------------------------------------------------------------------*)
type name_def = {
  n_fty : Type.ftype; (** restricted to: (Index | Timestamp)^* -> ty *)
}

(*------------------------------------------------------------------*)
type macro_def =
  | Input | Output | Cond | Exec | Frame
  | State of int * Type.ty
    (** Macro that expands to the content of a state at a given timestamp. *)
  | Global of int * Type.ty
    (** Global macros are used to encapsulate let-definitions.
        They are indexed. *)

(*------------------------------------------------------------------*)
type [@warning "-37"] param_kind =
  | PBool
  | PString
  | PInt

(*------------------------------------------------------------------*)
(** Information about symbol definitions, depending on the namespace.
    Integers refer to the index arity of symbols. *)
type _ def =
  | Channel  : unit      -> _channel def
  | Config   : param_kind-> _config def
  | Name     : name_def  -> _name    def
  | Action   : int       -> _action  def
  | Macro    : macro_def -> _macro   def
  | System   : unit      -> _system  def
  | Process  : unit      -> _process def
  | BType    : bty_infos -> _btype   def
  | HintDB   : unit      -> _hintdb  def
  | Lemma    : unit      -> _lemma   def
        
  | Function : (Type.ftype * function_def) -> _fname def
        
type edef =
  | Exists : 'a def -> edef
  | Reserved of namespace

(*------------------------------------------------------------------*)
(** {2 Data}
    In addition to their definition data, some more data can be attached
    to symbols. This is used for data that is defined in modules that
    depend on this module, through an extensible datatype. *)

(** Extensible type for data associated to symbols.
    Due to circular dependencies, this is not type-safe, but
    at least avoids having multiple hashtables for symbols. *)
type data = ..
type data += Empty
type data += AssociatedFunctions of fname list

(*------------------------------------------------------------------*)
(** {2 Basic namespace-independent operations} *)

(** Converts a symbol to a string, for printing purposes. *)
val to_string : 'a t -> string

(** Pretty-print a symbol. *)
val pp : Format.formatter -> 'a t -> unit

(** [def_of_lsymb s] returns the definition of the symbol named [s].
    @raise Unbound_identifier if no such symbol has been defined. *)
val def_of_lsymb : ?group:group -> lsymb -> table -> edef

val is_defined : ?group:group -> string -> table -> bool

type wrapped = Wrapped : 'a t * 'a def -> wrapped

(** [of_lsymb s] returns the symbol associated to [s]
    together with its defining data.
    @raise Unbound_identifier if no such symbol has been defined. *)
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

  val remove : table -> ns t -> table
    
  (** Reserve a fresh symbol name, resembling the given string. *)
  val reserve : table -> lsymb -> table * ns t

  (** Reserve a fresh symbol name. *)
  val reserve_exact : table -> lsymb -> table * ns t

  (** Release a reserved symbol. *)
  val release : table -> ns t -> table
    
  (** Define a symbol name that has been previously reserved
      using [fresh]. *)
  val define : table -> ns t -> ?data:data -> def -> table

  (** Redefine a symbol name that has been previously defined. *)
  val redefine : table -> ns t -> ?data:data -> def -> table

  (** Declare a new symbol, with a name resembling the given string,
      defined by the given value. *)
  val declare :
    table -> lsymb -> ?data:data -> def -> table * ns t

  (** Like declare, but use the exact string as symbol name.
      @raise Multiple_declarations if the name is not available. *)
  val declare_exact :
    table -> lsymb -> ?data:data -> def -> table * ns t

  val is_reserved : ns t -> table -> bool

  (** [mem s table] checks if [s] exists in this namespace. *)
  val mem       : ns t -> table -> bool
  val mem_lsymb : lsymb -> table -> bool

  (** [of_lsymb s] returns [s] as a symbol, if it exists in this namespace.
      @raise Unbound_identifier otherwise. *)
  val of_lsymb : lsymb -> table -> ns t

  (** [of_lsymb_opt s] returns [Some s] as a symbol, if it exists in this
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

  (** Map over the defined symbols of this namespace. *)
  val map : (ns t -> def -> data -> (def * data)) -> table -> table
end

module Config   : Namespace with type def = param_kind with type ns = _config
module Channel  : Namespace with type def = unit       with type ns = _channel
module BType    : Namespace with type def = bty_infos  with type ns = _btype
module Action   : Namespace with type def = int        with type ns = _action
module System   : Namespace with type def = unit       with type ns = _system
module Process  : Namespace with type def = unit       with type ns = _process
module HintDB   : Namespace with type def = unit       with type ns = _hintdb
module Lemma    : Namespace with type def = unit       with type ns = _lemma
                                                           
module Function : Namespace
  with type def = Type.ftype * function_def with type ns = _fname

module Macro    : Namespace with type def = macro_def with type ns = _macro
module Name     : Namespace with type def = name_def with type ns = _name

(*------------------------------------------------------------------*)
(** {2 Error Handling} *)

type error_i = 
  | Unbound_identifier    of string
  | Incorrect_namespace   of namespace * namespace (* expected, got *)
  | Multiple_declarations of string * namespace * group
  | Failure of string

type error = Location.t * error_i

val pp_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> error -> unit

exception Error of error

(*------------------------------------------------------------------*)
(** {2 Type information} *)

module TyInfo : sig
  type t = bty_info

  val parse : lsymb -> t

  (*------------------------------------------------------------------*)
  val get_bty_infos  : table -> Type.ty -> t list 
  val check_bty_info : table -> Type.ty -> t -> bool

  (*------------------------------------------------------------------*)
  (** Is the type a finite type, e.g. [Index] and [Timestamp] *)
  val is_finite : table -> Type.ty -> bool 

  (** Is the type is a fixed set (independent from the security 
      parameter η.
      (e.g. [Index], [Timestamp] and [Message]) *)
  val is_fixed : table -> Type.ty -> bool 

  (** Is the type well-founded for [Term.mk_lt], e.g. [Index], [Timestamp] 
      or [Message]. *)
  val is_well_founded : table -> Type.ty -> bool 
end

(*------------------------------------------------------------------*)
(** {2 Miscellaneous} *)

val is_infix     : fname -> bool 
val is_infix_str : string  -> bool 

val infix_assoc : fname -> assoc

val is_global : macro_def -> bool

(*------------------------------------------------------------------*)
(** {2 Builtins} *)

val builtins_table : table

(** Returns the type of a builtin function *)
val ftype_builtin : fname -> Type.ftype

(** Returns the type of a function *)
val ftype : table -> fname -> Type.ftype

(*------------------------------------------------------------------*)
(** {3 Action builtins} *)

val init_action : action

(*------------------------------------------------------------------*)
(** {3 Macro builtins} *)

val inp   : macro
val out   : macro
val cond  : macro
val exec  : macro
val frame : macro

(*------------------------------------------------------------------*)
(** {3 Channel builtins} *)

val dummy_channel_lsymb : lsymb
val dummy_channel : channel

(*------------------------------------------------------------------*)
(** {3 Function symbols builtins} *)

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

(** Witness *)

val fs_witness : fname

(** Successor over natural numbers *)

val fs_succ : fname

(** Adversary function *)

val fs_att : fname

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
val fs_zeroes : fname

(*------------------------------------------------------------------*)
module Ss (S : Namespace) : Set.S with type elt := S.ns t 
module Ms (S : Namespace) : Map.S with type key := S.ns t 
