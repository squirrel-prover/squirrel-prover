(** This module defines a notion of symbol with a global table of
    symbols.
    Each symbol has a symbol kind (e.g. an operator and a channel
    have different kinds), and each symbol is attached to a
    definition whose Ocaml type depends on the kind. *)

type lsymb = string Location.located

(*------------------------------------------------------------------*)
(** Type of a function symbol (Prefix or Infix)
    - infix symbols must start by an allowed character (see the lexer)
    - infix symbols must be without index parameters *)

type assoc = [`Right | `Left | `NonAssoc]
type symb_type = [ `Prefix | `Infix of assoc ]

(*------------------------------------------------------------------*)
(** ['a t] is the type of symbols of kind ['a]. *)
type 'a t

val hash : 'a t -> int

(** Symbol kind groups:
    symbols with the same name can exist in different symbol kind 
    groups. *)
type group

(** Type of tables of persistent symbol definitions.
    It is currently ineffective. *)
type table

(** Associates a unique tag to a table. For memoisation. *)
val tag : table -> int

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
type _theory

type channel   = _channel   t
type config    = _config    t
type oracle    = _oracle    t
type name      = _name      t
type action    = _action    t
type fname     = _fname     t
type macro     = _macro     t
type system    = _system    t
type process   = _process   t
type btype     = _btype     t
type game      = _game      t
type hintdb    = _hintdb    t
type lemma     = _lemma     t
type predicate = _predicate t
type theory    = _theory    t
    
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
  | Theory
    
val pp_symbol_kind : Format.formatter -> symbol_kind -> unit

val kind_of_string : ?group:group -> table -> string -> symbol_kind option
  
(*------------------------------------------------------------------*)
(** The status of a symbol. *)
type status =
  | Defined  of symbol_kind
  | Reserved of symbol_kind

val status_of_lsymb : ?group:group -> lsymb -> table -> status

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

(*------------------------------------------------------------------*)
(** {2 Basic kind-independent operations} *)

(** Converts a symbol to a string, for printing purposes. *)
val to_string : 'a t -> string

(** Pretty-print a symbol. *)
val pp : Format.formatter -> 'a t -> unit

val is_defined : ?group:group -> string -> table -> bool

(*------------------------------------------------------------------*)
(** {2 Symbol kinds} *)

(** Signature a new kind of symbols. *)
module type SymbolKind = sig

  (** Abstract type representing this kind. *)
  type ns
    
  val remove : table -> ns t -> table
    
  (** Reserve a fresh symbol name. *)
  val reserve : approx:bool -> table -> lsymb -> table * ns t

  (** Release a reserved symbol. *)
  val release : table -> ns t -> table
    
  (** Define a symbol name that has been previously reserved
      using [fresh]. *)
  val define : table -> ?data:data -> ns t -> table

  (** Redefine a symbol name that has been previously defined. *)
  val redefine : table -> ?data:data -> ns t -> table

  (** Declare a new symbol.
      @raise Multiple_declarations if the name is not available 
      and [not approx] holds. *)
  val declare :
    approx:bool -> table -> ?data:data -> lsymb -> table * ns t

  val is_reserved : ns t -> table -> bool

  (** [mem s table] checks if [s] exists for this kind. *)
  val mem       : string -> table -> bool
  val mem_lsymb : lsymb  -> table -> bool

  (** [of_lsymb s] returns [s] as a symbol, if it exists for this kind.
      @raise Unbound_identifier otherwise. *)
  val of_lsymb : lsymb -> table -> ns t

  (** Same as [of_lsymb_opt s] but using an option type *)
  val of_lsymb_opt : lsymb -> table -> ns t option

  (** [cast_of_string s] always returns [s] as a symbol. *)
  val cast_of_string : string -> ns t

  (** Get data associated to some symbol. *)
  val get_data : ns t -> table -> data

  (** [data_of_lsymb s] is equivalent to [get_data (of_lsymb s)]. *)
  val data_of_lsymb : lsymb -> table -> data

  (** Iterate on the defined symbols of this kind. *)
  val iter : (ns t -> data -> unit) -> table -> unit

  (** Fold over the defined symbols of this kind. *)
  val fold : (ns t -> data -> 'a -> 'a) -> 'a -> table -> 'a

  (** Map over the defined symbols of this kind. *)
  val map : (ns t -> data -> data) -> table -> table
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
module Theory    : SymbolKind with type ns = _theory
module Predicate : SymbolKind with type ns = _predicate
module Operator  : SymbolKind with type ns = _fname
module Macro     : SymbolKind with type ns = _macro
module Name      : SymbolKind with type ns = _name

(*------------------------------------------------------------------*)
(** {2 Error Handling} *)

type error_i = 
  | Unbound_identifier    of string
  | Incorrect_kind        of symbol_kind * symbol_kind (* expected, got *)
  | Multiple_declarations of string * symbol_kind * group
  | Failure of string

type error = Location.t * error_i

val pp_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> error -> unit

exception Error of error

(*------------------------------------------------------------------*)
(** {2 Sets and maps} *)

module Ss (S : SymbolKind) : Set.S with type elt := S.ns t 
module Ms (S : SymbolKind) : Map.S with type key := S.ns t 

(*------------------------------------------------------------------*)
(** {2 Some data definitions}

    Each symbol is defined by some data,
    whose type depends on the kind. *)

(*------------------------------------------------------------------*)
(** {3 Data definitions for operators (abstract and concrete)} 

    Contain the data definitions for concrete and abstract operators,
    except for some fields of concrete operators that are post-poned 
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
  val pp_abstract_def : Format.formatter -> abstract_def -> unit
        
  (*------------------------------------------------------------------*)
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

(** Extensible type for global macros:
    see to [macros.ml] for the single constructor of [global_macro_def].
    (the type is postponed because its definition uses terms, 
    which are defined after the [Symbols] module).  *)
type global_macro_def = ..

(** Extensible type for global macros:
    see to [macros.ml] for the single constructor of [global_macro_def].
    (the type is postponed because its definition uses terms, 
    which are defined after the [Symbols] module).  *)
type state_macro_def = ..

type macro_data =
  | Input | Output | Cond | Exec | Frame
  | State  of int * Type.ty * state_macro_def
  (** Stateful cells. *)
  | Global of int * Type.ty * global_macro_def
  (** Global macros are used to encapsulate let-definitions. *)
  
type data += Macro of macro_data

val get_macro_data : macro -> table -> macro_data

(*------------------------------------------------------------------*)
(** {3 Name data} *)

type name_data = {
  n_fty : Type.ftype; (** restricted to: (Index | Timestamp)^* -> ty *)
}

type data += Name of name_data

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

  (** Is the type enumerable in polynomial time *) 
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

val builtins_table : table

(** Returns the type of a builtin function *)
val ftype_builtin : fname -> Type.ftype

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
