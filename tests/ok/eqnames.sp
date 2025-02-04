hash h
name k : message

name n1 : message
name n2 : message

name m1 : index->message
name m2 : index->message

system null.

lemma different : n1 <> n2.
Proof.
 auto.
Qed.

lemma _ :
  forall (i:index,j:index),
  i <> j =>
  m1(i) <> m1(j).
Proof. intro *. eqnames.
 auto.
Qed.

(* check that `eqnames` does not work in the concrete logic *)
lemma _ :
  forall (i:index,j:index),
  i <> j =>
  m1(i) <> m1(j) <: Real.z.
Proof.
 checkfail auto exn GoalNotClosed.
 intro *. 
 checkfail eqnames exn Failure.
Abort.
 
