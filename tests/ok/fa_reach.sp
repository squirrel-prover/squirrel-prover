system null.

type fini [finite].
type fix [fixed,enum].

abstract a : index -> message.
abstract b : index -> message.

abstract a_fini : fini -> message.
abstract b_fini : fini -> message.

abstract a_fix : fix -> message.
abstract b_fix : fix -> message.

lemma _ :
 (forall (i : index), a(i) = b(i)) => 
 seq(i : index => a(i)) = seq(i : index => b(i)).
Proof.
  intro H. 
  fa.
  by rewrite H.
Qed.

lemma _ :
 seq(i : fix => a_fix(i)) = seq(i : fix => b_fix(i)) =>
 seq(i : fix => a_fix(i)) = seq(i : fix => b_fix(i)).
Proof.
  intro H.
  checkfail fa exn Failure.
  assumption.
Qed.

lemma _ :
 (forall (i : fini), a_fini(i) = witness) =>
 (forall (i : fini), b_fini(i) = witness) =>
 (forall(i : fini), a_fini(i) = witness) = (forall(i : fini), b_fini(i) = witness).
Proof.
  intro Ha Hb.
  checkfail fa exn Failure.
  by rewrite Ha Hb.
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

lemma _ :
    try find a : message such that a = witness in true else false
    = try find b : message such that b <> witness in false else true.
Proof.
    checkfail fa exn Failure.
Abort.

lemma _ :
    (forall (a : message), a = witness) = (forall (b : message), b = witness).
Proof.
   checkfail fa exn Failure.
Abort.

lemma _ :
    (forall (a : index), a = witness) = (forall (b : index), b = witness).
Proof.
   fa; auto.
Qed.

lemma _ i j : a i = b j.
Proof.
   fa.
Abort.

lemma _ i j : a i = b_fini j.
Proof.
   checkfail fa exn Failure.
Abort.
