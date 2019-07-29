(** Channels
  *
  * Channels are public and untyped.
  * A channel must be declared before being used. *)

type channel
type t = channel

val pp_channel : Format.formatter -> channel -> unit

val dummy : channel

(** [declare s] declares a channel named [s].
  * @raise Theory.Multiple_declaration if the channel is already declared. *)
val declare : string -> unit

(** [of_string s] retrieves the channel previously declared
  * under the name [s].
  * @raise Not_found if the channel is not declared. *)
val of_string : string -> channel

(** Forget all declarations, used for testing purposes. *)
val reset : unit -> unit
