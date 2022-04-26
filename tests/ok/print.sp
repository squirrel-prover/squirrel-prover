set autoIntro=false.

abstract a : message -> message

name n : index -> message
name m : message

channel c

system !_i out(c,<a(n(i)),a(m)>).

system [bis] null.

(*------------------------------------------------------------------*)
type T.
abstract ( -- ) : T -> T -> boolean.

axiom trans (x,y,z : T) : x -- y => y -- z => x -- z.

goal trans2 (x,y,z : T) : x -- y => y -- z => x -- z.
Proof. admit. Qed.

(*------------------------------------------------------------------*)
print goal trans.
print goal trans2.

goal _ : false.
Proof.
  print goal trans.
  print goal trans2.
Abort.

(*------------------------------------------------------------------*)
(* The main test, with a non-empty list of bound variables. *)
equiv foo (tau:timestamp,i:index) : output@tau, exec@tau.
Proof.
  (* print in equivalences *)
  print.
  print system [default].
  print system [bis].
  admit.
Qed.


(* The main test, with a non-empty list of bound variables. *)
goal bar : forall (tau, tau' : timestamp),
  output@tau = a(output@tau').
Proof.
  (* print in trace sequent *)
  print.
  print system [default].
  print system [bis].
  admit.
Qed.

