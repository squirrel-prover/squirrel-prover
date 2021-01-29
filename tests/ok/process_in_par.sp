channel c
system in(c,x) ; (in(c,x) | out(c,x)).

goal testA :
  output@A = empty.
Proof.
 by auto.
Qed.

goal testA1 :
  output@A1 = empty.
Proof.
 by auto.
Qed.

goal testA2 :
  output@A2 = input@A.
Proof.
 by auto.
Qed.
