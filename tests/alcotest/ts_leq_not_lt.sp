

abstract ok : message
channel c
system !_i A:out(c,ok).

lemma _ (i:index,j:index) : A(i) <= A(j) => A(i) < A(j).
Proof.
  intro Hle.
Qed.
