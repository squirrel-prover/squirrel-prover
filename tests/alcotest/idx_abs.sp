

abstract f : index->message

system null.

lemma _ (i,j:index) : f(i)=f(j) => i=j.
Proof.
  auto.
