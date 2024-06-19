mutable test(i: index) : message = zero.

abstract index_of_mess : message -> index.

channel pub.

process tutu = !_i A: in(pub,x); test (index_of_mess x) := x. 

system tutu.

lemma _ (i,j : index, t : timestamp) : 
  happens(A i) => 
  test j@A i = 
  if (j = index_of_mess (input@A(i))) then input@A(i) else test(j)@pred (A(i)).
Proof.
  intro ?.
  rewrite /test.
  auto.
Qed.
