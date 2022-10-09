system null.

abstract a : index -> message.
abstract b : index -> message.

goal _ : 
 (forall (i : index), a(i) = b(i)) => 
 seq(i : index => a(i)) = seq(i : index => b(i)).
Proof.
  intro H. 
  fa.
  by rewrite H.
Qed.

goal _ : 
 (forall (i : index), a(i) = b(i)) => 
 seq(i : index => a(i)) = seq(t : timestamp => zero).
Proof.
  intro H. 
  checkfail (try fa; rewrite H); auto exn GoalNotClosed.
Abort.

goal _ : 
 (forall (i : index), a(i) = b(i)) => 
 seq(i : index => a(i)) = seq(i : index, j : index => b(i)).
Proof.
  intro H. 
  checkfail (try fa; rewrite H); auto exn GoalNotClosed.
Abort.
