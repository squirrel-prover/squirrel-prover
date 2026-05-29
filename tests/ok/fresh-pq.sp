name n : message.

system [postquantum] null.

include Core.

set debugMacros=true.

lemma fresh_test (tau:_):
  (* fresh should not care if the LHS is ptime or pqtime or whatever. *)
  Quantum.input@tau=n => false.

Proof.
 intro Eq.
 fresh Eq.
Qed.

