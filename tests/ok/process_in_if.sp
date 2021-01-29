channel c
system
  in(c,x) ;
  if x = x then in(c,x) else out(c,x).

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
  output@A2 = input@A2.
Proof.
 by auto.
Qed.
