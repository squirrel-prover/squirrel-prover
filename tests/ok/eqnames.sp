set autoIntro=false.

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

goal independency :
  h(n1,k) <> n2.
Proof.
 intro Heq. simpl.
 by case H.
Qed.


goal independency_bis (i:index,j:index):
  i <> j =>
  h(m1(i),k) <> m1(j).
Proof.
 intro Hneq Heq. simpl.
 by case H.
Qed.
