channel c
system in(c,x); if False then A: out(c,x).

lemma _ (t:timestamp): happens(t) => happens(t).
Proof.
 auto.
Qed.
