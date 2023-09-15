abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

name n1 : index -> message
name m1 : message
name m2 : message

abstract ok : index   -> message
abstract f  : message -> message
abstract gg : message * message -> message
abstract f0 : message -> message
channel ch

mutable s : message = empty.

system A: !_i in(ch,x); new l; out(ch,<ok(i),<x,l>>).

system [bis] !_i in(ch,x); new l; if x = a then out(ch,<ok(i),<x,l>>).

global lemma _ : equiv(m1) -> equiv(m1).
Proof.
  nosimpl(intro H).
  apply H.
Qed.

global lemma _ : equiv(m1) -> equiv(m1).
Proof.
  nosimpl(intro H).
  auto.
Qed.

(*------------------------------------------------------------------*)
(* small tests with a `set` containing a single system *)
global lemma [set:default/left; equiv:default] _ : 
  equiv(diff(empty,zero), diff(zero,empty)).
Proof. 
  checkfail by deduce exn GoalNotClosed.
  checkfail deduce 1 exn ApplyMatchFailure.
  checkfail deduce 0 exn ApplyMatchFailure.
Abort.
