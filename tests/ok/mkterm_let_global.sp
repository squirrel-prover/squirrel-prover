set autoIntro=false.

channel c
system in(c,x);let y=x in out(c,x).

goal forall (t:timestamp), y@t = y@t.
Proof.
 auto.
Qed.
