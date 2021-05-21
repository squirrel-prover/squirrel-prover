(** Extends [LowTraceSequent] with function relying on the [Prover] module. *)
(* FIXME: redudancy with EquivTactics *)

open Utils

module SE = SystemExpr
module TS = LowTraceSequent

(*------------------------------------------------------------------*)
include TS 

(*------------------------------------------------------------------*)
let is_hyp_or_lemma (name : lsymb) (s : sequent) =
  Hyps.mem_name (L.unloc name) s || Prover.is_lemma (L.unloc name)

let is_equiv_hyp_or_lemma (name : lsymb) (s : sequent) =
  Hyps.mem_name (L.unloc name) s || Prover.is_equiv_lemma (L.unloc name)

let is_reach_hyp_or_lemma (name : lsymb) (s : sequent) =
  Hyps.mem_name (L.unloc name) s || Prover.is_reach_lemma (L.unloc name)

let get_hyp_or_lemma (name : lsymb) (s : sequent) =
  let lem =
    if Hyps.mem_name (L.unloc name) s then
      let id, f = Hyps.by_name name s in
      Goal.{ gc_name = `Hyp id;
             gc_system = system s;
             gc_tyvars = [];
             gc_concl = `Reach f; }
    else
      let lem = Prover.get_lemma name in
      { lem with gc_name = `Lemma lem.Goal.gc_name }
  in

  (* Verify that it applies to the current system. *)
  if not (SE.systems_compatible (TS.system s) lem.gc_system) then
    Tactics.hard_failure Tactics.NoAssumpSystem;

  lem

let get_reach_hyp_or_lemma name s =
  Goal.to_reach_lemma ~loc:(L.loc name) (get_hyp_or_lemma name s)

let get_equiv_hyp_or_lemma name s =
  Goal.to_equiv_lemma ~loc:(L.loc name) (get_hyp_or_lemma name s)

(*------------------------------------------------------------------*)
module Reduce = Reduction.Mk(LowTraceSequent)

let reduce s t = Reduce.reduce s t
