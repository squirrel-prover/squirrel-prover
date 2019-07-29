type args = (string * Theory.kind) list

val declare_goal :
  (args * Theory.fact) -> (args * Theory.fact)
  -> Theory.fact -> Theory.fact -> unit
