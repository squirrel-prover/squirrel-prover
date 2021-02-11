set autoIntro=false.

system null.

goal forall (t:timestamp), t <= pred(t) => False.
Proof.
 auto.
Qed.

goal forall (t:timestamp), t = pred(t) => not happens(t).
Proof.
 auto.
Qed.

goal forall (t:timestamp), happens(init).
Proof.
 auto.
Qed.
