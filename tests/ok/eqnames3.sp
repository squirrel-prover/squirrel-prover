type T[finite].

name n : T -> message.

name m : message.

system null.

global lemma _ : [forall i, n i <> m].
Proof.
  intro i.
  intro Eq.
  checkfail by eqnames exn GoalNotClosed.
Abort. 

global lemma _ (i : T) : [n i <> m].
Proof.
  intro /= Eq.
  checkfail by eqnames exn GoalNotClosed.
Abort. 

name k : T -> message.

global lemma _ (i, j : T) : [n i <> k j].
Proof.
  intro /= Eq.
  checkfail by eqnames exn GoalNotClosed.
Abort. 

global lemma _ (i : T[const]) (j : T) : [n i <> k j].
Proof.
  intro /= Eq.
  checkfail by eqnames exn GoalNotClosed.
Abort. 

global lemma _ (i : T) (j : T[const]) : [n i <> k j].
Proof.
  intro /= Eq.
  checkfail by eqnames exn GoalNotClosed.
Abort. 

global lemma _ (i : T[const]) (j : T[const]) : [n i <> k j].
Proof.
  intro /= Eq.
  by eqnames.
Qed. 

(* ------------------------------------------------------------------- *)
(* check of freshness, unrelated to `eqnames` *)
global lemma _ : [forall i, n i <> m].
Proof.
  intro i.
  intro Eq.
  checkfail fresh Eq exn Failure.
Abort.
