

name n : index->message
channel c

system !_i out(c,n(i)).

goal _ (i,j:index) : happens(A(i)) => n(i)=n(j) && cond@A(i) => cond@A(j).
Proof. 
  auto.
Qed.

goal _ (i,j:index) : happens(A(i)) => n(i)=n(j) => happens(A(j)).
Proof.
  auto.
Qed.
