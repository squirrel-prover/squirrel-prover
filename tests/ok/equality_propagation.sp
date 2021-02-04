set autoIntro=false.

name n : index->message

system null.

goal eq_timestamps :

  forall (tau1:timestamp, tau2:timestamp),
  tau1 = tau2 =>
  output@tau1 = output@tau2.

Proof.
 by auto.
Qed.

goal eq_names :

  forall (i:index, j:index),
  i<>j =>
  n(i) <> n(j).

Proof.
 by auto.
Qed.

goal functionality :
  forall (x:message, y:message),
  x = y => fst(x) = fst(y).
Proof.
 by auto.
Qed.

goal contradiction :
  forall (x:message, y:message),
  (x = y && x <> y) => False.
Proof.
  by auto.
Qed.
