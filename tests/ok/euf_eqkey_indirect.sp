(* Check that equality constraints on key indices are properly obtained
 * for indirect cases. *)

channel c
hash h
name n : message
name k : index->index->message

system !_i out(c,h(n,k(i,i))).

goal forall (tau:timestamp,a,b:index),
  output@tau = h(n,k(a,b)) =>
  a = b.
Proof.
  intros.
  nosimpl(euf M0).
  (* There should be one indirect case,
   * where a newly introduced index i should be
   * equal to both a and b. *)
  simpl.
Qed.
