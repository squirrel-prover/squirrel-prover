(** {1 Config Table} 
    Manipulation of Squirrel settings in the table. *)

(*------------------------------------------------------------------*)
type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int

type p_set_param = Symbols.lsymb * p_param_val

(*------------------------------------------------------------------*)
(** Initialize all setting to their default values in the table. *)
val init_params : Symbols.table -> Symbols.table

(** Change a setting in the table. *)
val set : Symbols.lsymb -> p_param_val -> Symbols.table -> Symbols.table

(*------------------------------------------------------------------*)
(** {2 Look-up functions} *)

(** Timeout for the solvers (completion.ml and constr.ml) in seconds. *)
val solver_timeout : Symbols.table -> int

(** Default value for [solver_timeout],
    used by functions which do not have access to the table for now. *)
val vint_timeout : int

(** Print equations of the TRS system. *)
val print_trs_equations : Symbols.table -> bool

(** Get boolean setting for interactive mode. *)
val interactive : Symbols.table -> bool

(** Name of the setting for interactive mode,
    to be used with [set_param]. *)
val s_interactive : string

(** Debug information for the constraint checker. *)
val debug_constr : Symbols.table -> bool

(** Debug information for the completion checker. *)
val debug_completion : Symbols.table -> bool

(** Debug information for tactics. *)
val debug_tactics : Symbols.table -> bool

(** Debug information for macros. *)
val debug_macros : Symbols.table -> bool

(** Strict alias mode for processes. *)
val strict_alias_mode : Symbols.table -> bool

(** Strict let mode for processes. *)
val strict_let_mode : Symbols.table -> bool

(** Show hypothesis after strengthening *)
val show_strengthened_hyp : Symbols.table -> bool

(** Automatic FA Dup. *)
val auto_fadup : Symbols.table -> bool

(** New equivalence induction principle. *)
val new_ind : Symbols.table -> bool

(** Post-quantum soundness. *)
val post_quantum : Symbols.table -> bool

(** Verbose mode for crypto tactic *)
val verbose_crypto : Symbols.table -> bool

(** Path to log unsatisfiability queries in crypto.
    An empty path [""] means that we should not log queries. *)
val log_unsat_crypto : Symbols.table -> string

(** Path to log membership deduction queries in crypto.
    An empty path [""] means that we should not log queries. *)
val log_mem_crypto : Symbols.table -> string

(** Pretty-print the refication of terms *)
val prettyprint_reify : Symbols.table -> bool
