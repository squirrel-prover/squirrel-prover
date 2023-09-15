include Basic.
channel c
system [T] (S : !_i !_i new n; out(c,n)).
lemma [T] foo (i:index) : happens(S(i,i)) => output@S(i,i) = n(i,i).
Proof.
admit.
Qed.
