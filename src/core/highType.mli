(** {1 Squirrel types}

    Contains declarations and functions operating on Squirrel's types
    that could not be done in the [Type] module due to circularity
    issues with [Symbols].
    (We use the structure [Type → Symbols → HighType].) *)

(*------------------------------------------------------------------*)
module Info : sig
  (** Type information associated to abstract types.
      Restrict the instantiation domain of a type. *)
  type t =
    | Large               (** collision probabiliy between names is negligible *)
    | Name_fixed_length   (** for any η, all names have the same length *)
    | Finite              (** finite for all η *)
    | Fixed               (** independent from η *)
    | Well_founded        (** well-founded for all η *)
    | Enum                (** enumerable in poly time  *)
    | Serializable        (** bit-string encodable *)

  (*------------------------------------------------------------------*)
  val parse : Symbols.lsymb -> t
end

(*------------------------------------------------------------------*)
type infos = Info.t list

type inductive_data = {
  ty_vars       : Ident.t list;   (** type parameters *)
  positive_vars : Ident.Sid.t;    (** is a type parameter used only in positive position *)
  negative_vars : Ident.Sid.t;    (** is a type parameter used only in negative position *)
  constructors  : Symbols.fname list;
}

type data =
  | Abstract of infos
  | Inductive of inductive_data

type Symbols.data += Type of data

(*------------------------------------------------------------------*)
val of_path : ?args:(Type.ty list) -> Symbols.ty -> Type.ty

(*------------------------------------------------------------------*)
val get_data : Symbols.ty -> Symbols.table -> data

val arity : Symbols.table -> Symbols.ty -> int

(*------------------------------------------------------------------*)
(** {2 Check that a type has some properties. } *)

val check_ty_info : Symbols.table -> Type.ty -> Info.t -> bool

(** Is the type a finite type, e.g. [Index] and [Timestamp] *)
val is_finite : Symbols.table -> Type.ty -> bool

(** Is the type a fixed set (independent from the security
    parameter η.
    (e.g. [Index], [Timestamp] and [Message]) *)
val is_fixed : Symbols.table -> Type.ty -> bool

(** The serializability order of the term. E.g. 
    - [message] is serializable as a bit-string (obviously), 
       and is thus order 0. 
    - [message -> message]              is order 1. 
    - [message -> message -> message]   is order 1.
    - [(message -> message) -> message] is order 2. 

    If [quantum] is [true], consider [quantum_message] as an order 0
    type ([quantum] default to [false]).

    Returns [None] if no order could be inferred (e.g. because there
    are type variables). *)
val serializability_order : 
  ?quantum:bool -> Symbols.table -> Type.ty -> int option

(** Are the element of the type all encodable as bit-strings *)
val is_bitstring_encodable : Symbols.table -> Type.ty -> bool

(** Is the type enumerable in polynomial time. *)
val is_enum : Symbols.table -> Type.ty -> bool

(** Are the names all of the same length. *)
val is_name_fixed_length : Symbols.table -> Type.ty -> bool

(** Is the type well-founded for [Term.mk_lt], e.g. [Index], [Timestamp]
    or [Message]. *)
val is_well_founded : Symbols.table -> Type.ty -> bool

(*------------------------------------------------------------------*)
(** Check if a type is definitely classical.
    A type is classical if its serializability order is at-most
    one. *)
val is_classical : Symbols.table -> Type.ty -> bool

(** Check if a type is definitely quantum.
    This is an approximation: if it returns [true], then the type 
    is quantum.  *)
val is_quantum : Type.ty -> bool

(*------------------------------------------------------------------*)
(** {3 Inductive types} *)
  
(** Is the type an inductive type. *)
val is_inductive : Symbols.table -> Type.ty -> bool

(** Return the construtors and the type argument of an inductive type,
    if applicable. *)
val constructors :
  Symbols.table -> Type.ty -> (Symbols.fname list * Type.ty list) option

(*------------------------------------------------------------------*)
(** {3 Applied ftypes} *)

val subst_of_applied_ftype : Type.applied_ftype -> Subst.t

(** apply a [ftype] to some type arguments *)
val apply_ftype : Type.ftype -> Type.ty list -> Type.ty
