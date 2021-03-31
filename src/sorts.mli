(** This modules provides the sorts used to typed variables and terms.
    The sort is explicit, so that we can construct terms as GADT over the
    sort. We provide ESort to wrap the explicit type. *)

type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]
type boolean   = [ `Boolean]

type _ sort =
  | Message   : message sort
  | Boolean   : boolean sort
  | Index     : index sort
  | Timestamp : timestamp sort

type 'a t = 'a sort

type esort = ESort : 'a sort -> esort

val eboolean   : esort
val emessage   : esort
val etimestamp : esort
val eindex     : esort

val equal : 'a sort -> 'b sort -> bool

val pp : Format.formatter -> 'a sort -> unit

val pp_e : Format.formatter -> esort -> unit
