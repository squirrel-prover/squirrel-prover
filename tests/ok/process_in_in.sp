set autoIntro=false.

channel c
system in(c,x);in(c,x);out(c,x).

goal testA :
  output@A = empty.
Proof.
 by auto.
Qed.

goal testA1 :
  output@A1 = input@A1.
Proof.
 by auto.
Qed.
