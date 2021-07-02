set autoIntro=false.

channel c
system (A: out(c,empty) | B: out(c,empty)).

axiom ab : A < B.

equiv [default/right,default/left] ab_left : diff(if A < B then empty,empty).
Proof.
  yesif 0.
  by use ab.
  auto.
Qed.
