set autoIntro=false.

name n : index->message
channel c
system !_i !_j out(c,n(j)).

goal _ (i:index,t:timestamp) : 
  n(i) = input@t => exists k:index, A(k,i) < t.
Proof.
  nosimpl(intro i t Heq).
  nosimpl(fresh Heq => [k G]).
  nosimpl(exists k).
  nosimpl(assumption).
Qed.
