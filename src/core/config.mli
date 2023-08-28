(*------------------------------------------------------------------*)
(** {2 parser types} *)

(** Parser parameter values *)
type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int

(** Parser parameter set *)
type p_set_param = string * p_param_val

(*------------------------------------------------------------------*)
(** {2 parameter state} *)

type params

val reset_params : unit -> unit

val get_params : unit -> params

val set_params : params -> unit

(*------------------------------------------------------------------*)
(** {2 look-up functions} *)

(** Debug information for the constraint checker. *)
val debug_constr : unit -> bool

(** Debug information for the completion checker. *)
val debug_completion : unit -> bool

(** Debug information for tactics. *)
val debug_tactics : unit -> bool

(** Old congruence closure. *)
val old_completion : unit -> bool

(*------------------------------------------------------------------*)
(** {2  set functions} *)

val set_param : p_set_param -> [`Failed of string | `Success]
