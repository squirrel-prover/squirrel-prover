

abstract ok : message
channel c
system A: out(c,ok).

lemma _: happens (A) => output@A XOR output@A = zero.
Proof.
 auto.
Qed.
