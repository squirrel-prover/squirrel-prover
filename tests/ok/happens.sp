set autoIntro=false.

channel c
system in(c,x); if False then A: out(c,x).

goal happens(A) => False.
Proof.
 auto.
Qed.

goal forall (t:timestamp), happens(t) => happens(t).
Proof.
 auto.
Qed.
