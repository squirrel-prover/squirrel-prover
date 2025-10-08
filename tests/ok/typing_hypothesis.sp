(* This file tests the tactics `typing`.
   The tactic checks, given [H : t1 = t2] that [t1] types Low and [t2] types High,
   or the opposite.
   We test here different combinaison of types for [t1] and [t2] *)

set securityTypes = true.

system sys = null.

name h : message, High
name l : message, Low
mutable s : message = empty.
name w : message. (*type wrong*)
lemma[sys] _ : h=l => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys] _ : l=h => false.
Proof.
  intro H.
  typing H.
Qed.
lemma[sys] _ : h=s@init => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : h=w => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : l=s@init => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : l=w => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : s@init=h => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : w=h => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : s@init=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
lemma[sys] _ : w=l => false.
Proof.
  intro H.
  checkfail typing H exn Failure.
Abort.
