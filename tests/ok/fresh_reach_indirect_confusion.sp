name n : index->message
channel c
system !_i !_j out(c,n(j)).

goal forall (i:index,t:timestamp) n(i) = input@t => exists k:index, A(k,i) < t.
Proof.
  nosimpl(intro i t Heq).
  nosimpl(fresh Heq).
  nosimpl(intro [k [j [H Hi]]]).
  nosimpl(exists k).
  nosimpl(substitute i,j).
  nosimpl(assumption).
Qed.
