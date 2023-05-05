(** Communication channels *)

(** As all channels are public and untyped,
  * channels are just identifiers.
  * They must be declared before being used. *)

type ns = Symbols.Channel.ns

type channel = ns Symbols.t
type t = channel

val pp_channel : Format.formatter -> channel -> unit

(** [of_lsymb s] retrieves the channel previously declared
  * under the name [s]. *)
val of_lsymb : Symbols.lsymb -> Symbols.table -> channel

(** [declare s] declares a channel named [s]. *)
val declare : Symbols.table -> Symbols.lsymb -> Symbols.table

(** Type of a parsed channel name *)
 type p_channel = string Location.located
