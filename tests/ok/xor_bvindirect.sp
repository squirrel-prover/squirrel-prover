set autoIntro=false.

(* Checking the treatment of bound variables in indirect cases for xor. *)

name n : index->message
name m : index->message

abstract ok : message
abstract ko : message

channel c

system !_i out(c,<n(i),seq(i->n(i))>).


axiom len_ok (i:index): len(ok) = len(n(i))
axiom len_ko (i:index): len(ko XOR m(i)) = len(n(i))
axiom len_ko_ok (i:index): len(ko XOR ok) = len(n(i)).

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (tau:timestamp,i:index) : output@tau, n(i) XOR diff(ok,m(i)).
Proof.
  xor 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall (i0,i1:index) A(i0)<=tau => i1 <> i && i0<>i),
    True.
  admit.
  nosimpl(yesif 1).

  by namelength n(i),m(i); use len_ok with i.

  fa 1.
  admit. (* Ignore final equivalence goal. *)
Qed.

(* The same test, but giving the fresh name as argument to the xor tactic. *)
equiv nonempty2 (tau:timestamp,i:index) :
  output@tau, ko XOR diff(ok,m(i)) XOR n(i).
Proof.
  xor 1, n(i).
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall (i0,i1:index) A(i0)<=tau => i1 <> i && i0<>i),
    True.
  admit.
  nosimpl(yesif 1).
  by use len_ko_ok with i; use len_ko with i.
  fa 1.
  admit. (* Ignore final equivalence goal. *)
Qed.
