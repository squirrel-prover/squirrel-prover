channel c
abstract ok : message

system A: if True then out(c,ok).

include Basic.

goal _: true || false.
Proof.
by left.
Qed.

goal _: false || true.
Proof.
by right.
Qed.

