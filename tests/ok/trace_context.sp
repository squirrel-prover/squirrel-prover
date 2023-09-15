name n : message.

lemma [any] _ (tau:timestamp) : output@tau <> n.
Proof.
  nosimpl intro H.
  checkfail fresh H exn Underspecified_system.
Abort.
