set autoIntro=false.

(* Checking the treatment of bound variables in indirect cases for prf. *)

hash h
name k : message

name n : index->message
name m : index->message

channel c

system !_i out(c,<h(n(i),k),seq(i:index ->h(n(i),k))>).

(* The main test, with a non-empty list of bound variables. *)
global goal nonempty (tau:timestamp,i:index) : 
[(diff(
       forall (i0:index), (A(i0) <= tau => n(i) <> n(i0)),
       forall (i0:index), (A(i0) <= tau => m(i) <> n(i0))) &&
  diff(
       forall (i0,i1:index), (A(i0) <= tau => n(i) <> n(i1)),
       forall (i0,i1:index), (A(i0) <= tau => m(i) <> n(i1)))) = true] ->
equiv(output@tau) ->
equiv(output@tau, diff(h(n(i),k),h(m(i),k))).
Proof.
  intro H E.
  prf 1.

  rewrite H.
  yesif 1; 1: auto.
  fresh 1.
  by apply E.
Qed.

