channel c.

name n : index -> message.

system !_i in(c,x);out(c,x).

goal foobar : forall (i,j:index)
  happens(A(i),A(j)) => A(i) = A(j) => n(i) = n(j).
Proof. 
  intro *.
  have ?: i = j by constraints.  
  congruence. 
Qed.
