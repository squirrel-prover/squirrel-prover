type args = (string * Theory.kind) list

val iter_goals : (Term.formula -> unit) -> unit

val declare_goal :
  (args * Theory.fact) -> (args * Theory.fact)
  -> Theory.fact -> Theory.fact -> unit
