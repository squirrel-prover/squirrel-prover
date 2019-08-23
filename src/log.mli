type log_class = LogConstr | LogTacticTC

val log : log_class -> (unit -> unit) -> unit

val start_log : log_class -> unit

val stop_log : log_class -> unit
