(** EUF-CMA obviously implies key privacy, because the attacker can forge
  * anything if he can recover the key from chosen-message attacks.
  * Here we carry out this argument formally in Squirrel. *)

hash h
name k : message
name fresh : message
channel c
system !_i in(c,x);out(c,h(x,k)).

goal forall t:timestamp, exec@t => input@t <> k.
Proof.
  intros.
  assert h(fresh,input@t) = h(fresh,k).
  euf M1.
  executable t. apply H1 to A(i).
  expand exec@A(i); expand cond@A(i).
  fresh M2.
Qed.
