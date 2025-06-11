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
      Returns [None] if no order could be inferred (e.g. because there
      are type variables). *)
val serializability_order : Symbols.table -> Type.ty -> int option

(** Is the type enumerable in polynomial time. *)
val is_enum : Symbols.table -> Type.ty -> bool

(** Are the names all of the same length. *)
val is_name_fixed_length : Symbols.table -> Type.ty -> bool

(** Is the type well-founded for [Term.mk_lt], e.g. [Index], [Timestamp]
    or [Message]. *)
val is_well_founded : Symbols.table -> Type.ty -> bool
