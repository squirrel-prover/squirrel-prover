channel c

system S : !_i new n; out(c,n).

goal foo :
  forall (i:index),
  output@S(i) = n(i).
Proof.
 simpl.
Qed.