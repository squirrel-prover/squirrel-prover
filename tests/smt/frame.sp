lemma[any] _ : frame@init=zero. Proof. smt. Qed.

lemma[any] _ (t:timestamp) : not (happens(t)) => frame@t=empty. Proof. smt. Qed. 
