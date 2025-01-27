(** Parameters

    This module manages user-definable parameters,
    as well as a few application parameters controlling how
    Squirrel runs. *)

(*------------------------------------------------------------------*)
(** {2 Types} *)

(** Parameter value *)
type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int

(** Parameter setting *)
type p_set_param = string * p_param_val

(*------------------------------------------------------------------*)
(** {2 Global parameter state} *)

type params

val reset_params : unit -> unit

val get_params : unit -> params

val set_params : params -> unit

(*------------------------------------------------------------------*)
(** {2 Getters} *)

(** Debug information for tactics. *)
val debug_tactics : unit -> bool

(*------------------------------------------------------------------*)
(** {2 Setters} *)

val set_param : p_set_param -> [`Failed of string | `Success]
