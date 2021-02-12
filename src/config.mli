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

(** timeout for the solver (completion.ml and constr.ml), in seconds. *)
val solver_timeout : unit -> int

(** Print equations of the TRS system. *)
val print_trs_equations : unit -> bool

(** Strict alias mode for processus. *)
val strict_alias_mode : unit -> bool

(** Automatic introductions (in hypotheses and the conclusion). *)
val auto_intro : unit -> bool

(*------------------------------------------------------------------*)
(** {2  set functions} *)

val set_param : p_set_param -> unit
