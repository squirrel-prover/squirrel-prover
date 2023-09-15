channel c
abstract ok : message

system A: if True then out(c,ok).

include Basic.

lemma _: true || false.
Proof.
by left.
Qed.

lemma _: false || true.
Proof.
by right.
Qed.

