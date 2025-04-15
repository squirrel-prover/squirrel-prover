include Core.

abstract t : int -> message.
axiom [any] t12 : t(12) = t(13).

lemma [any] _ : t(12) = t(13).
Proof.
simpl.
rewrite t12 //=.
Qed.

include Int.
open Int.

op x = 42.
op y : int = 42.

lemma [any] _ : 21 + 21 = 42.
Proof. 
  reduce ~flags:[builtin]. 
  true.
Qed.

lemma [any] _ : 21 * 2 = 42.
Proof. 
  reduce ~flags:[builtin]. 
  true.
Qed.

lemma [any] _ : 44 - 2 = 42.
Proof. 
  reduce ~flags:[builtin]. 
  true.
Qed.

lemma [any] _ : 24 <> 42.
Proof. 
  reduce ~flags:[builtin]. 
  true.
Qed.

lemma [any] _ : 24 < 42.
Proof.
  reduce ~flags:[builtin]. 
  true.
Qed.

lemma [any] _ : 24 <= 24 && 24 <= 42.
Proof. 
  reduce ~flags:[builtin]. 
  split; true.
Qed.

lemma [any] _ : 42 > 24.
Proof. 
  reduce ~flags:[builtin]. 
  true.
Qed.

lemma [any] _ : 24 >= 24 && 42 >= 24.
Proof. 
  reduce ~flags:[builtin]. 
  split; true.
Qed.


lemma [any] _ : 42 <= 24.
Proof.
  checkfail auto exn GoalNotClosed.
Abort.


lemma [any] _ : 24 >= 42.
Proof.
  checkfail auto exn GoalNotClosed.
Abort.

lemma [any] _ : 42 < 24.
Proof.
  checkfail auto exn GoalNotClosed.
Abort.


lemma [any] _ : 24 > 42.
Proof.
  checkfail auto exn GoalNotClosed.
Abort.
