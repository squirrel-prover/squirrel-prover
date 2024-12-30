system null.

abstract p : index -> bool.

global lemma [set: default/left; equiv:default] _ :
  (Forall i, [p i]) -> [forall i, p i].
Proof.
  intro H.
  intro i.
  have A := H i.
  assumption A.
Qed.

(* same lemma, but in set `default` (thus, the global forall cannot be
   instantiated). *)
global lemma [set: default; equiv:default] _ :
  (Forall i, [p i]) -> [forall i, p i].
Proof.
  intro H.
  intro i.
  checkfail (have A := H i) exn Failure.
Abort.
