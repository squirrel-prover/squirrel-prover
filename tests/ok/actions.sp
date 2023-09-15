channel c.

system S : !_i new n; out(c,n).

lemma foo (i:index) : happens(S(i)) => output@S(i) = n(i).
Proof.
 auto.
Qed.
