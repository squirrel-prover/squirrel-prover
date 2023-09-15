channel c
system in(c,x) ; (in(c,x) | out(c,x)).

lemma testA :
  happens(A) => output@A = empty.
Proof.
 auto.
Qed.

lemma testA1 :
  happens(A1) => output@A1 = empty.
Proof.
 auto.
Qed.

lemma testA2 :
  happens(A2) => output@A2 = input@A.
Proof.
 auto.
Qed.
