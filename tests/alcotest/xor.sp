

include Basic.

name n1 : message

abstract ok : message
abstract ko : message

channel c

system out(c,<n1,diff(xor(n1,ok),xor(n1,ko))>).

equiv test.
Proof.
induction t; try auto.
expandall.
fa 0.
fa 1.
fa 1.
fa 1.
xor 2.
rewrite if_false in 2; 1: auto.
simpl.
Qed.
