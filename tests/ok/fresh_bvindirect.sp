(* Checking the treatment of bound variables in indirect cases for fresh. *)

name n : index->message
name m : index->message

channel c

system !_i out(c,<n(i),seq(i:index => n(i))>).

include Basic.

(* The main test, with a non-empty list of bound variables. *)
global goal nonempty (tau:timestamp[const],i:index[const]) :
  [(forall (i1,i0:index), (A(i0) <= tau => i <> i1))
   = true ] ->
  equiv(output@tau) ->
  equiv(output@tau, diff(n(i),m(i))).
Proof.
  intro H H1.
  fresh 1.
  (* Check that the right formula has been produced using H *)
  by rewrite H.
  auto.
Qed.
