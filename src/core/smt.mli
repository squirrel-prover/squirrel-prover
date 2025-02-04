(** [is_valid ... free_variables hypotheses conclusion]
    attempts to verify that [conclusion] follows from [hypotheses]
    for all [free_variables].
    This is done through a translation to SMT solvers,
    which is guaranteed correct but not complete.
    Other arguments allow to tweak this translation. *)
val is_valid :
  macro_axioms:bool ->
  timeout:int ->
  steps:int option -> 
  provers:(string*string) list->
  cmd_flag:string ->
  poly:bool ->
  exact:bool ->
  hint_tables:string list ->
  Env.t -> 
  Symbols.table ->
  < > SystemExprSyntax.expr ->
  Vars.var list ->
  Term.term list ->
  (Hint.smt_hint list) Utils.Ms.t ->
  Term.term ->
  bool
