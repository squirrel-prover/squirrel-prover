

name n : index->message
channel c
system !_i !_j out(c,n(j)).

lemma _ (i:index,t:timestamp) : 
  n(i) = input@t => exists k, A(k,i) < t.
Proof.
  intro Heq.
  fresh Heq. intro [k G].
  exists k. constraints.
Qed.
