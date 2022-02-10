set autoIntro=false.

(* Checking the treatment of bound variables in indirect cases for fresh. *)

name n : index->message
name m : index->message

channel c

system !_i out(c,<n(i),seq(i:index ->n(i))>).

(* The main test, with a non-empty list of bound variables. *)
global goal nonempty (tau:timestamp,i:index) :
  [(forall (i0,i1:index), (A(i0) <= tau => i1 <> i))
   = true ] ->
  equiv(output@tau) ->
  equiv(output@tau, diff(n(i),m(i))).
Proof.
  intro H H1.
  fresh 1.
  (* Check that the right formula has been produced using H *)
  rewrite H.
  yesif 1; 1: auto.
  auto.
Qed.
