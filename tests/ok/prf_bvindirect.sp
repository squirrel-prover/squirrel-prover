set autoIntro=false.

(* Checking the treatment of bound variables in indirect cases for prf. *)

hash h
name k : message

name n : index->message
name m : index->message

channel c

system !_i out(c,<h(n(i),k),seq(i->h(n(i),k))>).

(* The main test, with a non-empty list of bound variables. *)
equiv nonempty (tau:timestamp,i:index) : output@tau, diff(h(n(i),k),h(m(i),k)).
Proof.
  prf 1.
  (* Check that the right formula has been produced,
     using an incorrect equivalence that we admit. *)
  equivalent
    (forall (i0,i1:index),
      (diff((A(i0) <= tau => (n(i) <> n(i1) && n(i) <> n(i0))),
	          (A(i0) <= tau => (m(i) <> n(i1) && m(i) <> n(i0)))))),
    True.
  admit.
  yesif 1; 1: auto.
  fresh 1.
  admit. (* Ignore final equivalence goal. *)
Qed.
