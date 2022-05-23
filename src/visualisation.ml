(** Write in /tmp/dump.js the content of the model in JSON format **)
let dump () =
  let out_c = open_out "/tmp/dump.js" in
  let ppf = Format.formatter_of_out_channel out_c in
  match Prover.get_first_subgoal () with
  | Trace j -> Constr.dump ppf (LowTraceSequent.mk_trace_cntxt j)
  | Equiv j -> ();
  close_out out_c
