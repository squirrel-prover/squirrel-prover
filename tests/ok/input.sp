channel c
system in(c,x);out(c,x).

goal test :
  output@A = input@A.
Proof.
 by auto.
Qed.
