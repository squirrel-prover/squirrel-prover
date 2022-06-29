abstract a : message -> message

name n : index -> message
name m : message

channel c

system !_i out(c,<a(n(i)),a(m)>).

system [bis] null.

(*------------------------------------------------------------------*)
type T.
abstract ( -- ) : T -> T -> boolean.

axiom mtrans (x,y,z : T) : x -- y => y -- z => x -- z.

goal trans2 (x,y,z : T) : x -- y => y -- z => x -- z.
Proof. admit. Qed.

(*------------------------------------------------------------------*)
print goal mtrans.
print goal trans2.

goal _ : false.
Proof.
  print goal mtrans.
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

(*------------------------------------------------------------------*)
abstract ok : message

system [s1] in(c,x); let S=diff(<x,ok>,x) in A : out(c,S).

system [s2] in(c,x); let St=diff(x,<x,ok>) in A : out(c,St).

(* sanity checks *)
print system [s1/left, s2/right].
print system [s2/left, s1/right].
print system [s1/left].
print system [s2/left].
print system [s1/right].
print system [s2/right].
