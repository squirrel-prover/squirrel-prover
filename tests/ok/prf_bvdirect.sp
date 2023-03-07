

include Basic.

(* Checking the treatment of bound variables in direct cases for prf. *)

hash h
name k : message
name n : index->message
name m : index->message

system null.

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (i:index[param]) : 
  seq(i,y:index => h(n(i),k)), h(diff(n(i),m(i)),k).
Proof.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  have H:
    (forall (i0:index), (diff(n(i) <> n(i0), m(i) <> n(i0)))) =
    true.
  admit. 
  prf 1.
  + rewrite H. true.
  + rewrite H. true.
  + auto.
Qed.

(* Secondary test, without any bound variable, just to check
   that an empty forall is not produced. *)
equiv empty (i:index[param]) : 
  h(n(i),k), h(diff(n(i),m(i)),k).
Proof.
   (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  have H:
    (diff(n(i), m(i)) <> n(i)) = true.
  admit.
  prf 1.
  + auto.
  + rewrite H; admit.
  + auto.
Qed.
