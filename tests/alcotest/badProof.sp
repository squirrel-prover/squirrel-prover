(* This lemma's proof is purposedly invalid (as `toto` does not
   exists), to check that `include[admit]` does ignore proofs. *)
lemma [any] _ : false.
Proof. by apply toto. Qed.
