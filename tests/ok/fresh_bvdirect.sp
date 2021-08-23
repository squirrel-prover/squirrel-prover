set autoIntro=false.

(* Checking the treatment of bound variables in direct cases for fresh. *)

name n : index->message
name m : index->message

system null.

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (i:index) : seq(i:index ->n(i)), diff(n(i),m(i)).
Proof.
  fresh 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall i0:index, i<>i0),
    True.
  admit.
  nosimpl(yesif 1).
  true.
  refl.
Qed.

(* Secondary test, without any bound variable, just to check
   that an empty forall is not produced. *)
equiv empty (i:index) : n(i), diff(n(i),m(i)).
Proof.
  fresh 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (i<>i),
    True.
  admit.
  nosimpl(yesif 1).
  true.
  refl.
Qed.
