lemma[any] _ : false. Proof. checkfail smt exn Failure. Abort.

lemma[any] _ : true. Proof. smt. Qed.
