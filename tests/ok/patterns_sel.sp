set autoIntro=false.

abstract a : message -> message

name n : index -> message
name m : message

channel c

system !_i out(c,<a(n(i)),a(m)>).

(* The main test, with a non-empty list of bound variables. *)
goal bar : forall (tau, tau' : timestamp, i:index),
  output@tau = try find i such that true in output@tau else a(m).
Proof.
  intro tau tau' i0.
  printmessages a(_).
  printmessages (try find i such that _ in _ else a(m)).
  case (try find i such that _ in _ else a(m)).
  intro [i [H ->]] //.

  intro [H _]. use H with i0.
  auto.
Qed.
