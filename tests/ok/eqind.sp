

hash h
name k : message

name m1 : index -> message

system null.

lemma function (i:index,j:index) :
  i = j =>
  m1(i) = m1(j).
Proof.
 auto.
Qed.
