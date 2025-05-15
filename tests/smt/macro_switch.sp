channel c.

system S = out(c,empty).

lemma _ @system:S : happens(A) => init <= A.
Proof.
  smt.
Qed.

lemma _ @system:S : happens(A) => init <= A.
Proof.
  smt ~no_macros.
Qed.

lemma _ @system:S : happens(A) => output@A = empty.
Proof.
  smt.
Qed.

lemma _ @system:S : happens(A) => output@A = empty.
Proof.
  checkfail (smt ~no_macros) exn Failure.
Abort.
