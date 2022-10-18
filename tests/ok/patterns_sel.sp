

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
  show a(_).
  show (try find i such that _ in _ else a(m)).
  case (try find i such that _ in _ else a(m)).
  intro [i [H ->]] //.

  intro [H _].
  by use H with i0.
Qed.

goal foo : forall (tau, tau' : timestamp, i:index),
  output@tau = try find i such that n(i)=n(i) in output@tau else a(m).
Proof.
  intro tau tau' i0.
  show a(_).

  show (try find i such that n(i)=n(i) in _ else a(m)).


  show (try find i0 such that n(i0)=n(i0) in _ else a(m)).

  show (try find i0 such that n(i0)=n(i0) in output@tau else _).


 (* following command fails and should not*)
  show try find i such that _ in _ else a(m).
  show try find i0 such that _ in output@tau else a(m).

  (* following command fails, but maybe there is no solution *)
  (* show (try find i such that _ in _ else _). *)

Abort.
