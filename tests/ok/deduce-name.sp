name s : message.
channel c.

system out(c,s). 

(* Simple name management *)

global lemma _ : equiv(s,s) -> equiv(s).
Proof.
  intro H.
  apply H.
Qed.

global lemma _ : equiv(s) -> equiv(s,s).
Proof.
  intro H.
  apply H.
Qed.

global lemma _ : equiv(s).
Proof.
  checkfail deduce 0 exn ApplyMatchFailure.
  auto.
Qed.

