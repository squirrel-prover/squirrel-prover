channel c
system in(c,x);out(c,x);in(c,x);out(c,x).

goal test :
  output@A1 = input@A1.
Proof.
 simpl.
Qed.