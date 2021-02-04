set autoIntro=false.

abstract f : index->message

system null.

goal forall (i,j:index) f(i)=f(j) => i=j.
Proof.
  auto.
