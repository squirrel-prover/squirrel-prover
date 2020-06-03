hash h
name k : index->message
name n : index->index->message
abstract ok : message

system null.

goal forall (j,j1,j2:index),
  seq(i,j -> h(n(i,j),k(i))) = h(n(j1,j2),k(j)) => j1=j2.
Proof.
  intros.
  euf M0.
  (* This should not complete the proof.
   * There should be one goal, corresponding to a possible
   * equality between n(j1,j2) and an instance of n(_,_)
   * inside the seq(_). *)
Qed.
