include Core.
set smtSteps=10000.

lemma[any] _ : cond@init. Proof. smt. Qed. 

lemma[any] _ (t:timestamp) : cond@t => (happens(t)). Proof. smt. Qed.
