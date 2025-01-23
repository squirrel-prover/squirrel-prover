include DeductionSyntax.

system P = null.

global lemma [P] _ : $(( empty )|> ( empty )).
Proof.
simpl.
have Hapi0 : (witness = diff(0,1)) by admit.
simpl. (* used to yield an anomaly (see #291) *)
Abort.
