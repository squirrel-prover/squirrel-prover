include Basic.

(* Checking the treatment of bound variables in direct cases for xor. *)

name n : index->message
name m : index->message

abstract ok : message
abstract ko : message

system null.

axiom len_ok_ko (i:index): len(ok XOR ko) = len(n(i))
axiom len_ko_ok (i:index): len(ko XOR ok) = len(m(i))
axiom len_ok (i:index): len(ok) = len(n(i))
axiom len_ko (i:index): len(ko) = len(m(i)).

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (i:index) :
  seq(i:index => n(i)), diff(ok XOR ko XOR n(i),ko XOR ok XOR m(i)).
Proof.
  xor 1, diff(n(i),m(i)).
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  have ->:
    (forall i0:index, i<>i0) = true.
  admit.
  nosimpl(rewrite if_true in 1).
  by use len_ok_ko with i; use len_ko_ok with i.
  refl.
Qed.

(* Secondary test, without any bound variable, just to check
   that an empty forall is not produced. *)
equiv empty (i:index[const]) : n(i), diff(n(i) XOR ok,m(i) XOR ko).
Proof.
  xor 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  have ->:
    (i<>i) =
    True.
  admit.
  nosimpl(rewrite if_true in 1).
  by use len_ok with i; use len_ko with i.
  refl.
Qed.
