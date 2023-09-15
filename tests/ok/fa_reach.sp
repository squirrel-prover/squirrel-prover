system null.

abstract a : index -> message.
abstract b : index -> message.

lemma _ : 
 (forall (i : index), a(i) = b(i)) => 
 seq(i : index => a(i)) = seq(i : index => b(i)).
Proof.
  intro H. 
  fa.
  by rewrite H.
Qed.

lemma _ : 
 (forall (i : index), a(i) = b(i)) => 
 seq(i : index => a(i)) = seq(t : timestamp => zero).
Proof.
  intro H. 
  checkfail (try fa; rewrite H); auto exn GoalNotClosed.
Abort.

lemma _ : 
 (forall (i : index), a(i) = b(i)) => 
 seq(i : index => a(i)) = seq(i : index, j : index => b(i)).
Proof.
  intro H. 
  checkfail (try fa; rewrite H); auto exn GoalNotClosed.
Abort.
