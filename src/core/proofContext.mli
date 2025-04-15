(** A local proof-context is an environment (of type [Env.t]) enriched
    with some hypotheses. *)

(*------------------------------------------------------------------*)
module SE = SystemExprSyntax
module TraceHyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
(** a proof-context *)
type t = private {
  env  : Env.t;
  hyps : Hyps.TraceHyps.hyps;
  tag  : int;
}

(* Tag enabling hash consing *)
val tag : t -> int

(*------------------------------------------------------------------*)
val make : env:Env.t -> hyps:TraceHyps.hyps -> t

(*------------------------------------------------------------------*)
(** Change the system of a proof-context, dropping hypotheses if
    needed (see [Hyps.change_trace_hyps_context]). *)
val change_system : system:SE.context -> t -> t
