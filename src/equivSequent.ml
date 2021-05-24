(** Extends [LowEquivSequent] with function relying on the [Prover] module *)

open Utils

module SE = SystemExpr
module ES = LowEquivSequent

(*------------------------------------------------------------------*)
include ES

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
             gc_concl = `Equiv f; }
    else
      let lem = Prover.get_lemma name in
      { lem with gc_name = `Lemma lem.Goal.gc_name }
  in

  (* Verify that it applies to the current system. *)
  if not (SE.systems_compatible (ES.system s) lem.gc_system) then
    Tactics.hard_failure Tactics.NoAssumpSystem;

  lem

let get_reach_hyp_or_lemma name s =
  let lem = get_hyp_or_lemma name s in
  if Goal.is_reach_lemma lem 
  then Goal.to_reach_lemma ~loc:(L.loc name) lem
  else
    let lem = Goal.to_equiv_lemma lem in
    { lem with Goal.gc_concl = ES.form_to_reach lem.gc_concl }

let get_equiv_hyp_or_lemma name s =
  Goal.to_equiv_lemma ~loc:(L.loc name) (get_hyp_or_lemma name s)

(*------------------------------------------------------------------*)
module Reduce = Reduction.Mk(LowEquivSequent)

let reduce s e = Reduce.reduce_equiv s e
