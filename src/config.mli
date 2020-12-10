(*------------------------------------------------------------------*)
(* parser types *)

(** Parser parameter values *)
type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int     

(** Parser parameter set *)
type p_set_param = string * p_param_val


(*------------------------------------------------------------------*)
(* parameter state *)

type params

val get_params : unit -> params 

val set_params : params -> unit

(*------------------------------------------------------------------*)
(* look-up functions *)

(** timeout for the solver (completion.ml and constr.ml), in seconds. *)
val solver_timeout      : unit -> int

(** Print equations of the TRS system. *)
val print_trs_equations : unit -> bool


(*------------------------------------------------------------------*)
(* set function *)

val set_param : p_set_param -> unit
