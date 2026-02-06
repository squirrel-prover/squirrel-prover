name n : message.

system null.

include Core.

lemma fresh_test (tau:_):
  (* fresh should not care if the LHS is ptime or pqtime or whatever. *)
  Quantum.input@tau=n => false.

Proof.
 intro Eq.
 fresh Eq.
Qed.

