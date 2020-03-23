name n : message
name m : message
name k : message
abstract u : message

hash h

channel c
system !_i out(c,<h(n,k),h(m,k)>).

goal forall tau:timestamp, output@tau = h(u,k) => False.
Proof.
  intros.
  nosimpl(euf M0).
  (* Here EUF should create two cases for action A(_).
   * In each case a fresh index variable i should be created;
   * there should not be a second index variable i1 in the
   * second case. *)
  simpl.
  assert (i1=i1).
