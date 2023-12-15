(** {1 Config Table} 
    Manipulation of Squirrel settings in the table. *)

(** Reset all setting to their default values in the table. *)
val reset_params : Symbols.table -> Symbols.table

(** Change a setting in the table. *)
val set_param : (string * Config.p_param_val) -> Symbols.table -> Symbols.table

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

(** Setting for checking proofs in included files. *)
val checkInclude : Symbols.table -> bool

(** Debug information for the constraint checker. *)
val debug_constr : Symbols.table -> bool

(** Debug information for the completion checker. *)
val debug_completion : Symbols.table -> bool

(** Debug information for tactics. *)
val debug_tactics : Symbols.table -> bool

(** Strict alias mode for processus. *)
val strict_alias_mode : Symbols.table -> bool

(** Show hypothesis after strengthening *)
val show_strengthened_hyp : Symbols.table -> bool

(** Automatic FA Dup. *)
val auto_fadup : Symbols.table -> bool

(** New equivalence induction principle. *)
val new_ind : Symbols.table -> bool

(** Post-quantum soundness. *)
val post_quantum : Symbols.table -> bool