type log_class = LogConstr

let runtime_logs = ref [LogConstr]

let log cls f = if List.mem cls !runtime_logs then f () else ()

let start_log cls =
  runtime_logs :=
    if List.mem cls !runtime_logs then !runtime_logs else cls :: !runtime_logs

let stop_log cls =
  runtime_logs := List.fold_left (fun acc x ->
      if x = cls then acc else x :: acc
    ) [] !runtime_logs
