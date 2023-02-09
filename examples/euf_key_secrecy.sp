(** EUF-CMA obviously implies key privacy, because the attacker can forge
  * anything if he can recover the key from chosen-message attacks.
  * Here we carry out this argument formally in Squirrel. *)

set postQuantumSound=true.

hash h
name k : message.
name nfresh : message.
channel c
system !_i in(c,x);out(c,h(x,k)).

goal _ (t:timestamp[param]): happens(t) => input@t <> k.
Proof.
  intro _ _.
  assert h(nfresh,input@t) = h(nfresh,k) as Heuf; 1: auto.
  euf Heuf.
  intro [i [_ H]]; by fresh H.
Qed.
