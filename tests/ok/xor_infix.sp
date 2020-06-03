abstract ok : message
channel c
system A: out(c,ok).

goal output@A XOR output@A = zero.
Proof.
 simpl.
Qed.
