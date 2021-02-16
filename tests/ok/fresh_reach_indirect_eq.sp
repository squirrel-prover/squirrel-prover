set autoIntro=false.

name n : index->message

channel c

system !_i out(c,n(i)).

goal _ (j:index,t:timestamp) : n(j) = input@t => A(j) < t.
Proof.
  nosimpl(intro i t Heq).
  nosimpl(fresh Heq).
  nosimpl(intro H).
  nosimpl(assumption).
Qed.
