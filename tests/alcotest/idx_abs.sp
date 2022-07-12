

abstract f : index->message

system null.

goal _ (i,j:index) : f(i)=f(j) => i=j.
Proof.
  auto.
