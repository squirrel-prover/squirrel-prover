hash h
name k : message

name n1 : message
name n2 : message

name m1 : index->message
name m2 : index->message

system null.

goal different : n1 <> n2.
Proof.
 auto.
Qed.

goal injectivity :
forall (i:index,j:index),
i <> j =>
 m1(i) <> m1(j).
Proof.
 auto.
Qed.
 
