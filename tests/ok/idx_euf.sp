hash h (1)
name k : message

abstract a : message
abstract b : message
abstract f : message->message

system null.

goal forall (i,j:index) f(h(i,a,k)) = h(j,b,k) => a = b.
Proof.
  nosimpl(intros).
  nosimpl(euf M0).
  (* Since i=j is possible, EUF should not dismiss the hash of a. *)
  assumption.
Qed.
