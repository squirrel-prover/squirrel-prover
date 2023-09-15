ddh g, (^), ( ** ).

name a : message.
name b : message.
name k : message.

system null.

global lemma _ (x:message) : equiv(g^x).
Proof.
  ddh g, a, b, k.
Qed.

