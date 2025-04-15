module SE = SystemExprSyntax
module TraceHyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
(** a proof-context *)
type t = {
  env  : Env.t;
  hyps : Hyps.TraceHyps.hyps;
  tag  : int;
}

let tag t = t.tag

(*------------------------------------------------------------------*)
let cpt = ref 0

let make ~env ~hyps =
  incr cpt;
  { env; hyps; tag = !cpt; }

(*------------------------------------------------------------------*)
let change_system ~(system : SE.context) (t : t) : t =
  let hyps =
    Hyps.change_trace_hyps_context
      ~vars:Vars.empty_env
      (* FIXME: extend type [t] with the variable env and use it
         here *)
      ~old_context:t.env.system
      ~new_context:system
      ~table:t.env.table
      t.hyps
  in
  let env = { t.env with system; } in
  make ~env ~hyps
