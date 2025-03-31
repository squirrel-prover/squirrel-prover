(** Style for translating timestamps. *)
type timestamp_style =
  | Abstract     (** Abstract with specific ~~ for comparison. *)
  | Abstract_eq  (** Abstract with builtin equality for comparison. *)
  | Nat          (** Natural numbers. *)

(** [is_valid ... free_variables hypotheses conclusion]
    attempts to verify that [conclusion] follows from [hypotheses]
    for all [free_variables].
    This is done through a translation to SMT solvers,
    which is guaranteed correct but not complete.
    Other arguments allow to tweak this translation. *)
val is_valid :
timestamp_style:timestamp_style ->
  separate_tuple:bool -> 
  timeout:int ->
  steps:int option -> 
  provers:(string*string) list->
  Symbols.table ->
  SystemExpr.fset option ->
  Vars.var list ->
  Term.term list ->
  Term.term ->
  bool