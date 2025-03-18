set timeout=10.

lemma[any] _  : exec@init. Proof. smt. Qed.

lemma[any] _ (t:timestamp) : not (happens(t)) => not (exec@t). Proof. smt. Qed.

lemma[any] _ (ts,t:timestamp) : (exec@ts && t<=ts) => exec@t. Proof. smt. Qed.
