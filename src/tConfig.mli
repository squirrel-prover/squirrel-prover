(*------------------------------------------------------------------*)
(** {2 parameter state} *)
val reset_params : Symbols.table -> Symbols.table

type p_param_val = Config.p_param_val

val declare : Symbols.table -> Theory.lsymb -> p_param_val ->
  Symbols.table

(*------------------------------------------------------------------*)
(** {2 look-up functions} *)

(** timeout for the solver (completion.ml and constr.ml), in seconds. *)
val solver_timeout : Symbols.table -> int

val vint_timeout : int

(** Print equations of the TRS system. *)
val print_trs_equations : Symbols.table -> bool

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

(** Automatic introductions (in hypotheses and the conclusion). *)
val auto_intro : Symbols.table -> bool

(** Automatic FA Dup. *)
val auto_fadup : Symbols.table -> bool

(** New equivalence induction principle. *)
val new_ind : Symbols.table -> bool

(** Old congruence closure. *)
val old_completion : Symbols.table -> bool

(** Post-quantum soundness. *)
val post_quantum : Symbols.table -> bool

(*------------------------------------------------------------------*)
(** {2  set functions} *)

val set_param : (string * p_param_val) -> Symbols.table -> Symbols.table

