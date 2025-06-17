(*------------------------------------------------------------------*)
(* check that `destruct` handles tuple equalities *)

lemma [any] _ ['a 'b] (i1,i2 : 'a, j1,j2 : 'b) :
  (i1,j1) = (i2,j2) => i1 = i2 && j1 = j2.
Proof.
  intro [H1 H2]. 
  split. 
  + assumption H1.
  + assumption H2.
Qed.

lemma [any] _ ['a 'b 'c] (i1,i2 : 'a, j1,j2 : 'b, k1,k2 : 'c) :
  (i1,j1,k1) = (i2,j2,k2) => i1 = i2 && j1 = j2 && k1 = k2.
Proof.
  intro [H1 H2 H3]. 
  split; 2:split. 
  + assumption H1.
  + assumption H2.
  + assumption H3.
Qed.

(*------------------------------------------------------------------*)
(* same on inductive types *)

inductive MyTuple a b = 
| T : a -> b -> MyTuple a b.

lemma [any] _ ['a 'b 'c] (i1,i2 : 'a, j1,j2 : 'b) :
  T i1 j1 = T i2 j2 => i1 = i2 && j1 = j2.
Proof.
  intro [H1 H2].
  split. 
  + assumption H1.
  + assumption H2.
Qed.

inductive C a = 
| A : a -> C a
| B : a -> C a.

lemma [any] _ ['a] (i1,i2 : 'a, a1,a2 : 'a) :
  A i1 = A i2 => i1 = i2.
Proof. 
  intro [H]. 
  assumption H.
Qed.


lemma [any] _ ['a] (i1,i2 : 'a, a1,a2 : 'a) :
  A i1 = B i2 => i1 = i2.
Proof. 
  checkfail intro [H] exn Failure.
Abort.
