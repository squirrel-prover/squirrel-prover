(* Check that equality constraints on key indices are properly obtained
 * for direct cases. *)

hash h
name n : message
name k : index->index->message

system null.

goal forall (a,b,i:index),
  h(n,k(i,i)) = h(n,k(a,b)) =>
  a = b.
Proof.
  intros.
  nosimpl(euf M0).
  (* There should be one direct case,
   * where index i should be equal to both a and b. *)
  simpl.
Qed.
