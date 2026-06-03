(** A local proof-context is an environment (of type [Env.t]) enriched
    with some hypotheses and a boolean indicating whether we are in a
    concrete judgement. *)

(*------------------------------------------------------------------*)
module SE = SystemExprSyntax
module TraceHyps = Hyps.TraceHyps

(*------------------------------------------------------------------*)
(** a proof-context *)
type t = private {
  env      : Env.t;
  hyps     : Hyps.TraceHyps.hyps;
  concrete : bool;
  tag      : int;
}

(* Tag enabling hash consing *)
val tag : t -> int

(*------------------------------------------------------------------*)
(** Test physical equality of the fields, excluding [tag] *)
val equal_fields : t -> t -> bool

(*------------------------------------------------------------------*)
(* Makes a proof context. if [global] is true, the proof context is
   meant to be used to reason under global predicates, in which case,
   only global hypothesis in hyps are kept. *) 
val make : env:Env.t -> hyps:TraceHyps.hyps ->
  global:bool -> concrete:bool -> t

(*------------------------------------------------------------------*)

(* Invariant: for all the following functions, we assumed that t was
   initialized with the correct ~global field in the first call to
   make. *)

(** Change the system of a proof-context, dropping hypotheses if
    needed (see [Hyps.change_trace_hyps_context]). *)  
val change_system : system:SE.context -> t -> t

val set_env      : Env.t               -> t -> t
val set_hyps     : Hyps.TraceHyps.hyps -> t -> t
val set_vars     : Vars.env            -> t -> t
val set_table    : Symbols.table       -> t -> t
val set_concrete : bool                -> t -> t
