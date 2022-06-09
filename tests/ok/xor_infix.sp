

abstract ok : message
channel c
system A: out(c,ok).

goal _: happens (A) => output@A XOR output@A = zero.
Proof.
 auto.
Qed.
