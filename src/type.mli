(** This modules provides the types used to type variables and terms.
    The type is explicit, so that we can construct terms as GADT over it. *)

type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]
type boolean   = [ `Boolean]

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

val eboolean   : ety
val emessage   : ety
val etimestamp : ety
val eindex     : ety

val equal : 'a ty -> 'b ty -> bool

val pp : Format.formatter -> 'a ty -> unit

val pp_e : Format.formatter -> ety -> unit
