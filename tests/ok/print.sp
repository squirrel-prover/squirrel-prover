set autoIntro=false.

abstract a : message -> message

name n : index -> message
name m : message

channel c

system !_i out(c,<a(n(i)),a(m)>).

(* The main test, with a non-empty list of bound variables. *)
equiv foo (tau:timestamp,i:index) : output@tau, exec@tau.
Proof.
  (* print in equivalences *)
  print.
  admit.
Qed.


(* The main test, with a non-empty list of bound variables. *)
goal bar : forall (tau, tau' : timestamp),
  output@tau = a(output@tau').
Proof.
  (* print in trace sequent *)
  print.
  admit.
Qed.
