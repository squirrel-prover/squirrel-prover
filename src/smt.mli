val literals_unsat :
  slow:bool ->
  Symbols.table ->
  SystemExpr.fset ->
  Vars.var list ->
  Term.xatom list ->
  Term.literals ->
  Term.term list ->
  bool
