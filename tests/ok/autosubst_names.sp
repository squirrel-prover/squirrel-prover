name n : index->message
channel c

system !_i out(c,n(i)).

goal forall (i,j:index), n(i)=n(j) && cond@A(i) => cond@A(j).
Proof.
  intro *.
Qed.
