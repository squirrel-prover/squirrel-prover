(** Checking compatibility conditions when using an assumption (other than an hypothesis).
  * Currently compatibility verification is different for "rewrite" and "use"
  * so we should have separate tests for "rewrite". *)

abstract a : message
abstract b : message
system [s1] null.
system [s2] null.

axiom [s1] ax1 : a=b.
axiom [s2] ax2 : a=b.
axiom [s1/left] ax1l : a=b.
axiom [s1/right] ax1r : a=b.
axiom [s2/left] ax2l : a=b.
axiom [s2/right] ax2r : a=b.

goal [s1/right] _ : a=b.
Proof. 
  checkfail use ax2 exn NoAssumpSystem.
  checkfail use ax1l exn NoAssumpSystem.
  use ax1r.
  assumption.
Qed.

global goal [s1/right,s1/left] _ : [a=b].
Proof.
  byequiv.
  checkfail use ax2 exn NoAssumpSystem.
  checkfail use ax1l exn NoAssumpSystem.
  use ax1.
  assumption.
Qed.

global goal [s1/right,s1/left] _ : [a=b].
Proof.
  byequiv.
  checkfail use ax2 exn NoAssumpSystem.
  checkfail use ax1l exn NoAssumpSystem.
  project.
    + checkfail use ax1l exn NoAssumpSystem.
      apply ax1r.
    + checkfail use ax1r exn NoAssumpSystem.
      apply ax1l.
Qed.

global goal [s1/right,s1/left] _ (x:message) : [x=a] -> equiv(diff(x,b)).
Proof.
  intro H.
  use ax1 as HH.
  rewrite H; rewrite HH; auto.
Qed.
