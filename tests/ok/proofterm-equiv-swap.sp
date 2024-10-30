(* Test that equivalences are properly swapped when the corresponding
   system annotation is swapped in proof terms. *)

system N = null.

abstract a : message.
abstract b : message.

global axiom [set: N/left; equiv: N/left,N/right] ax : equiv(diff(a,b)).

global lemma [set: N/left; equiv: N/right,N/left] _ : equiv(diff(a,b)).
Proof.
  checkfail apply ax exn ApplyMatchFailure.
Abort.
