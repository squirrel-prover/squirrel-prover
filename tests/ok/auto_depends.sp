channel c.

system P = A: out(c,empty); B: out(c,zero).

lemma [P] _ : happens(B) => happens(A).
Proof. constraints. Qed.

(* same using `auto` *)
lemma [P] _ : happens(B) => happens(A).
Proof. auto. Qed.

lemma [P] _ : happens(B) => output@A = empty.
Proof. auto. Qed.

lemma [P] _ : happens(B) => output@A = empty.
Proof. rewrite /output. auto. Qed.
