set autoIntro=false.

(* Checking the treatment of bound variables in direct cases for prf. *)

hash h
name k : message
name n : index->message
name m : index->message

system null.

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (i:index) : seq(i->h(n(i),k)), diff(h(n(i),k),h(m(i),k)).
Proof.
  prf 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall (i1:index), (diff(n(i) <> n(i1), m(i) <> n(i1)))),
    True.
  admit.
  yesif 1.
Qed.

(* Secondary test, without any bound variable, just to check
   that an empty forall is not produced. *)
equiv empty (i:index) : h(n(i),k), diff(h(n(i),k),h(m(i),k)).
Proof.
  prf 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (diff(n(i), m(i)) <> n(i)),
    True.
  admit.
  yesif 1.
Qed.
