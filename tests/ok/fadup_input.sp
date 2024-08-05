channel c
name n : message
abstract ok : message
abstract ko : message

system A:  in(c,x);out(c,x);
       A1: in(c,x);out(c,x).

(* This is allowed as input@A = g(frame@pred(A)). *)
global lemma test_pred : equiv(input@A, frame@pred(A)).
Proof. 
  deduce 0. 
  nosimpl(admit 0).
  refl.
Qed.

global lemma test_pred_t (t:timestamp[adv]) : equiv(input@t, frame@pred(t)).
Proof.
  nosimpl(deduce 0).
  nosimpl(admit 0).
  refl.
Qed.

(* Same as before, using additionnally frame@pred(t) = fst(frame@t). *)
global lemma test (t:timestamp[adv]) : equiv(input@t, frame@t).
Proof.
  nosimpl(deduce 0).
  nosimpl(admit 0).
  refl.
Qed.

(* Same as above, because A1 must occur after A. *)
global lemma test_depends : equiv(input@A, frame@A1).
Proof.
  deduce 0.
  nosimpl(admit 0).
  refl.
Qed.


global lemma test_depends_att : equiv(frame@A) -> equiv(input@A1).
Proof.
  intro H.
  checkfail (deduce 0) exn  ApplyMatchFailure.
Abort.
