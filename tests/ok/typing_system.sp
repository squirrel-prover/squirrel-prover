(* This file tests the tactics `typing`.
   We test that, when `typing` is called, we have a finite set of well-typed
   systems.
   Here, [sys] is defined such that the left projection is well-typed and not
   the right one *)

set securityTypes = true.

channel c
name h : message, High
name l : message, Low.

system sys = (in(c, x); out(c,diff(l,h))).

lemma[sys/left] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys/right] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[any] _ : h=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys/right,sys/left] _ : diff(empty,h)=l => false.
Proof.
  project; intro H.
  checkfail typing H exn Failure.
  cycle 1.
  typing H.
Abort.
