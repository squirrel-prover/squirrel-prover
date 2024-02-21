abstract foo : message
system null.

global lemma one (tau:timestamp) :
  equiv(frame@pred(tau)) ->
  equiv(frame@pred(tau), input@tau).
Proof.
  nosimpl(intro H).
  nosimpl(apply H).
Qed.

global lemma two (tau:timestamp) :
  equiv(frame@pred(tau)) ->
  equiv(frame@pred(tau), exec@pred(tau) && output@pred(tau) = foo).
Proof.
  nosimpl(intro H).
  nosimpl(apply H).
Qed.


global lemma three (tau:timestamp) :
  equiv(frame@pred(tau)) ->
  equiv(frame@pred(tau), output@pred(tau) = foo).
Proof.
  nosimpl(intro H).
  checkfail deduce 1 exn ApplyMatchFailure.
  admit 1.
  auto.
Qed.
