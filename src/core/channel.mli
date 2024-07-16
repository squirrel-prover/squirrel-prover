(** Communication channels *)

open Utils
    
(** As all channels are public and untyped.
    They must be declared before being used. *)

type t = Symbols.channel

val pp_channel : t formatter

(** [of_lsymb table p] retrieves the channel previously declared
    under the name [p] in [table]. *)
val convert : Symbols.table -> Symbols.p_path -> t

(** [declare s] declares a channel named [s]. *)
val declare : Symbols.table -> Symbols.lsymb -> Symbols.table
