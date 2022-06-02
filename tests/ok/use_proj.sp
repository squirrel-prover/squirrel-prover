

include Basic.

channel c
system (A: out(c,empty) | B: out(c,empty)).

axiom ab : A < B.

equiv [default/right,default/left] ab_left : diff(if A < B then empty,empty).
Proof.
  rewrite if_true in 0.
  by use ab.
  auto.
Qed.
