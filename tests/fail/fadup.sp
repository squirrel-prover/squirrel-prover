set autoIntro=false.

abstract foo : message
system null.

equiv one (tau:timestamp) : frame@pred(tau) -> frame@pred(tau), input@tau.
Proof.
  nosimpl(intro H).
  nosimpl(fadup).
  assumption.
Qed.

equiv two (tau:timestamp) : frame@pred(tau) ->
                            frame@pred(tau), exec@pred(tau) && output@pred(tau) = foo.
Proof.
  nosimpl(intro H).
  checkfail (fadup;assumption) exn NotHypothesis.
  nosimpl(fadup 1).
  fadup; assumption.
Qed.

equiv three (tau:timestamp) : frame@pred(tau) ->
                              frame@pred(tau), output@pred(tau) = foo.
Proof.
  nosimpl(intro H).
  checkfail fadup 1 exn Failure.
  admit 1.
Qed.
