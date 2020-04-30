(* Checking the treatment of bound variables in direct cases for prf inside a context. *)

hash h
name k : message
name n : index->message
name m : index->message

system null.

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (i:index) : seq(i->h(n(i),k)), diff(h(n(i),k),h(m(i),k)).
Proof.
  prf 0.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall (i1:index), (diff(n(i) <> n(i1), m(i) <> n(i1)))),
    True.
  admit.
  yesif 1.
Qed.
