channel c
system in(c,x) ; (in(c,x) | out(c,x)).

goal testA :
  output@A = empty.
Proof.
 simpl.
Qed.

goal testA1 :
  output@A1 = empty.
Proof.
 simpl.
Qed.

goal testA2 :
  output@A2 = input@A.
Proof.
 simpl.
Qed.