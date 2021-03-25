(** EUF-CMA obviously implies key privacy, because the attacker can forge
  * anything if he can recover the key from chosen-message attacks.
  * Here we carry out this argument formally in Squirrel. *)

hash h
name k : message
name fresh : message
channel c
system !_i in(c,x);out(c,h(x,k)).

goal _ (t:timestamp):
 happens(t) => exec@t => input@t <> k.
Proof.
  intro *.
  assert h(fresh,input@t) = h(fresh,k).
  euf Meq0.
  executable t. use H0 with A(i).
  expand exec@A(i); expand cond@A(i).
  fresh Meq1.
Qed.
