

(* Checking the treatment of bound variables in direct cases for fresh. *)

name n : index->message
name m : index->message

system null.

include Basic.

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (i:index[const]) : seq(i:index => n(i)), diff(n(i),m(i)).
Proof.
  fresh 1.
  (* Check that the right formula has been produced,
     using an incorrect formula that we admit. *)
  + assert (forall i0:index, i<>i0) by admit.
    assumption.
  + refl.
Qed.

(* Secondary test, without any bound variable, just to check
   that an empty forall is not produced. *)
equiv empty (i:index[const]) : n(i), diff(n(i),m(i)).
Proof.
  fresh 1.
  (* Check that the right formula has been produced,
     using an incorrect formula that we admit. *)
  + assert (i<>i) by admit.
    assumption.
  + refl.
Qed.
