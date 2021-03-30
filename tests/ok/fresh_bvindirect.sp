set autoIntro=false.

(* Checking the treatment of bound variables in indirect cases for fresh. *)

name n : index->message
name m : index->message

channel c

system !_i out(c,<n(i),seq(i->n(i))>).

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (tau:timestamp,i:index) : output@tau, diff(n(i),m(i)).
Proof.
  fresh 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall (i0,i1:index) A(i0)<=tau => i1 <> i && i0<>i),
    True.
  admit.
  nosimpl(yesif 1).
  true.
  admit. (* Ignore final equivalence goal. *)
Qed.
