(* Regression test: namelength axioms should be generated for all names
   generated by tactics, not only the first one. *)
hash h.
name k1 : message.
name k2 : message.
system null.
global goal _ : equiv(len(h(zero,k1)),len(h(zero,k2))).
Proof.
  prf 0.
  prf 1.
  rewrite namelength_n_PRF.
  rewrite namelength_n_PRF1.
  refl.
Qed.
