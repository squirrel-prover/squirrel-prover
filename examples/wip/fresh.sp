name n1 : message
name n2 : message
name n3 : message

channel c

system out(c,n1); out(c,diff(xor(n3,n1), xor(n3,n2) )).

equiv test.
Proof.
induction t.
expandall.
fa 1.
fa 2.
fresh 2.
(* A possible way of concluding the proof.*)
yesif 2.
depends A,A1.
expandall.
fa 1.
fa 2.
xor 2.

Qed.
