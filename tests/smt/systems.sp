channel c.
system S1 = A: out(c,empty); out(c,zero).
system S2 = A: out(c,zero); out(c,empty).

(* S1 *)

lemma [S1] _ : happens(A) => output@A = empty.
Proof. smt. Qed.

lemma [S1] _ : happens(A1) => happens(A).
Proof. smt. Qed.

(* S2 *)

lemma [S2] _ : happens(A) => output@A = zero.
Proof. smt. Qed.

lemma [S2] _ : happens(A1) => happens(A).
Proof. smt. Qed.

(* any

   We just make sure smt supports any.
   We cannot test anything more specific as we can't even talk
   about actions. *)

lemma [any] _ : true.
Proof. smt. Qed.

(* any like *)

lemma [any/S1] _ : happens(A) => output@A = zero.
Proof. checkfail smt exn Failure. Abort.

lemma [any/S1] _ : happens(A) => output@A = empty.
Proof. checkfail smt exn Failure. Abort.

lemma [any/S1] _ : happens(A1) => happens(A).
Proof. smt. Qed.
