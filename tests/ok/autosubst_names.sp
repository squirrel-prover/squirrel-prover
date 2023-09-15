

name n : index->message
channel c

system !_i out(c,n(i)).

lemma _ (i,j:index) : happens(A(i)) => n(i)=n(j) && cond@A(i) => cond@A(j).
Proof. 
  auto.
Qed.

lemma _ (i,j:index) : happens(A(i)) => n(i)=n(j) => happens(A(j)).
Proof.
  auto.
Qed.
