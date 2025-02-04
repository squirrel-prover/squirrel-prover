module SE = SystemExprSyntax
module TraceHyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
(** a proof-context *)
type t = {
  env      : Env.t;
  hyps     : Hyps.TraceHyps.hyps;
  concrete : bool;
  tag      : int;
}

let tag t = t.tag

(*------------------------------------------------------------------*)
let cpt = ref 0

let make ~env ~hyps ~concrete =
  incr cpt;
  { env; hyps; concrete; tag = !cpt; }

(*------------------------------------------------------------------*)
let change_system ~(system : SE.context) (t : t) : t =
  let hyps =
    Hyps.change_trace_hyps_context
      ~vars:t.env.vars
      ~old_context:t.env.system
      ~new_context:system
      ~table:t.env.table
      t.hyps
  in
  let env = { t.env with system; } in
  make ~env ~hyps ~concrete:t.concrete

(*------------------------------------------------------------------*)
let set_env (env : Env.t) (t : t) : t =
  make ~env ~hyps:t.hyps ~concrete:t.concrete

let set_hyps (hyps : Hyps.TraceHyps.hyps) (t : t) : t =
  make ~env:t.env ~hyps ~concrete:t.concrete

let set_vars (vars : Vars.env) (t : t) : t =
  let env = Env.set_vars t.env vars in
  make ~env ~hyps:t.hyps ~concrete:t.concrete

let set_table (table : Symbols.table) (t : t) : t =
  let env = Env.set_table t.env table in
  make ~env ~hyps:t.hyps ~concrete:t.concrete

let set_concrete (concrete : bool) (t : t) : t =
  make ~env:t.env ~hyps:t.hyps ~concrete 
