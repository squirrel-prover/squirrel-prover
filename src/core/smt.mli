val literals_unsat :
  slow:bool ->
  Symbols.table ->
  SystemExpr.fset ->
  Vars.var list ->
  Term.Lit.xatom list ->
  Term.Lit.literals ->
  Term.term list ->
  bool
