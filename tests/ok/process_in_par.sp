set autoIntro=false.

channel c
system in(c,x) ; (in(c,x) | out(c,x)).

goal testA :
  happens(A) => output@A = empty.
Proof.
 by auto.
Qed.

goal testA1 :
  happens(A1) => output@A1 = empty.
Proof.
 by auto.
Qed.

goal testA2 :
  happens(A2) => output@A2 = input@A.
Proof.
 by auto.
Qed.
