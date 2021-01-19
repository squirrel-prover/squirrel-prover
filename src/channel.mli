(** Communication channels *)

(** As all channels are public and untyped,
  * channels are just identifiers.
  * They must be declared before being used. *)

type ns = Symbols.Channel.ns

type channel = ns Symbols.t
type t = channel

val pp_channel : Format.formatter -> channel -> unit

(** [of_string s] retrieves the channel previously declared
  * under the name [s].
  * @raise Not_found if the channel is not declared. *)
val of_string : string -> Symbols.table -> channel

(** [declare s] declares a channel named [s].
  * @raise Theory.Multiple_declaration if the channel is already declared. *)
val declare : Symbols.table -> string -> Symbols.table

(** Type of a parsed channel name *)
 type p_channel = string Location.located
