

channel c
system
  in(c,x) ;
  if x = x then in(c,x) else out(c,x).

goal testA :
  happens(A) => output@A = empty.
Proof.
 auto.
Qed.

goal testA1 :
  happens(A1) => output@A1 = empty.
Proof.
 auto.
Qed.

goal testA2 :
  happens(A2) => output@A2 = input@A2.
Proof.
 auto.
Qed.
