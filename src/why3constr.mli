val literals_unsat :
  slow:bool ->
  Symbols.table ->
  SystemExpr.t ->
  Vars.evar list ->
  Term.message_atom list ->
  Term.trace_literal list ->
  Term.message list ->
  bool
