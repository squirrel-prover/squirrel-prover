(** This modules provides the types used to type variables and terms.
    The type is explicit, so that we can construct terms as GADT over it. *)

type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]
type boolean   = [ `Boolean]

(*------------------------------------------------------------------*)
type _ ty =
  (** Built-in sorts *)
  | Message   : message ty
  | Boolean   : boolean ty
  | Index     : index ty
  | Timestamp : timestamp ty

  (** User-defined types (kind Message) *)
  | TBase     : string -> message ty
        
  (** Type variable (kind Message) *)
  | TVar      : Ident.t -> message ty

type 'a t = 'a ty

type ety = ETy : 'a ty -> ety

(*------------------------------------------------------------------*)
val eboolean   : ety
val emessage   : ety
val etimestamp : ety
val eindex     : ety


(*------------------------------------------------------------------*)
(** Kinds of types *)
type _ kind =
  | KMessage   : message   kind
  | KBoolean   : boolean   kind
  | KIndex     : index     kind
  | KTimestamp : timestamp kind

val kind : 'a ty -> 'a kind
    
(*------------------------------------------------------------------*)
(** Equality witness for kinds *)
type (_,_) kind_eq = Kind_eq : ('a, 'a) kind_eq

(** Equality witness for types *)
type (_,_) type_eq = Type_eq : ('a, 'a) type_eq

(*------------------------------------------------------------------*)
(** Sub-typing relation, and return a (Ocaml) type equality witness *)
val subtype_w : 'a ty -> 'b ty -> ('a,'b) type_eq option

val subtype   : 'a ty -> 'b ty -> bool

(*------------------------------------------------------------------*)
(** Equality relation, and return a (Ocaml) type equality witness *)
val equal_w : 'a ty -> 'b ty -> ('a,'b) type_eq option

val equal   : 'a ty -> 'b ty -> bool

(*------------------------------------------------------------------*)
val pp : Format.formatter -> 'a ty -> unit

val pp_e : Format.formatter -> ety -> unit
