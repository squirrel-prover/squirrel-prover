

abstract foo : message
system null.

global goal one (tau:timestamp) :
  equiv(frame@pred(tau)) ->
  equiv(frame@pred(tau), input@tau).
Proof.
  nosimpl(intro H).
  nosimpl(fadup).
  assumption.
Qed.

global goal two (tau:timestamp) :
  equiv(frame@pred(tau)) ->
  equiv(frame@pred(tau), exec@pred(tau) && output@pred(tau) = foo).
Proof.
  nosimpl(intro H).
  checkfail (fadup;assumption) exn NotHypothesis.
  nosimpl(fadup 1).
  fadup; assumption.
Qed.

global goal three (tau:timestamp) :
  equiv(frame@pred(tau)) ->
  equiv(frame@pred(tau), output@pred(tau) = foo).
Proof.
  nosimpl(intro H).
  checkfail fadup 1 exn Failure.
  admit 1.
  auto.
Qed.
