channel c
abstract ok:message

system in(c,x); if x=ok && x<>ok then out(c,x).

equiv test.
Proof.
induction t.

expand frame@A.
expand exec@A.
equivalent cond@A, False.
expand cond@A.

fa 0.

expand frame@A1.
expand exec@A1.
equivalent cond@A1, True.
expand cond@A1.

fa 0.

Qed.
