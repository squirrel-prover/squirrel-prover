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

(** Debug information for the constraint checker. *)
val debug_constr : unit -> bool

(** Debug information for the completion checker. *)
val debug_completion : unit -> bool

(** Debug information for tactics. *)
val debug_tactics : unit -> bool

(** Strict alias mode for processus. *)
val strict_alias_mode : unit -> bool

(** Show hypothesis after strengthening *)
val show_strengthened_hyp : unit -> bool
    
(** Automatic introductions (in hypotheses and the conclusion). *)
val auto_intro : unit -> bool

(** Automatic FA Dup. *)
val auto_fadup : unit -> bool

(** New equivalence induction principle. *)
val new_ind : unit -> bool

(*------------------------------------------------------------------*)
(** {2  set functions} *)

val set_param : p_set_param -> unit
