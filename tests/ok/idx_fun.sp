set autoIntro=false.

abstract id : index->message

hash h (2)
name k : message

system null.

goal _ (i:index): id(i)=id(i).
Proof.
  auto.
Qed.

goal _ (x:message,i,j:index): h(i,j,x,k) = x.
