include Basic.

(* Checking the treatment of bound variables in indirect cases for prf. *)

hash h
name k : message

name n : index->message
name m : index->message

channel c

abstract one : message.

system !_i out(c,<h(<zero,n(i)>,k),seq(i:index => h(<one,n(i)>,k))>).

(* The main test, with a non-empty list of bound variables. *)
global goal _ (tau:timestamp[param],i:index[param]) : 
  [(diff(
         forall (i0:index), (A(i0) <= tau => n(i) <> <zero,n(i0)>),
         forall (i0:index), (A(i0) <= tau => m(i) <> <zero,n(i0)>)) &&
    diff(
         forall (i0,i1:index), (A(i0) <= tau => n(i) <> <one,n(i1)>),
         forall (i0,i1:index), (A(i0) <= tau => m(i) <> <one,n(i1)>))) = true] ->
  equiv(output@tau) ->
  equiv(output@tau, diff(h(n(i),k),h(m(i),k))).
Proof.
  intro H E.
  prf 1.

  rewrite H.
  rewrite if_true in 1; 1: auto.
  fresh 1; 1:auto.
  by apply E.
Qed.

(*------------------------------------------------------------------*)
(* same system, but using [one] both times: therefore, the occurrence outside 
   the sequences is redundant, and should not appear when applying the PRF 
   rule. *)
system [bis] !_i out(c,<h(<one,n(i)>,k),seq(i:index => h(<one,n(i)>,k))>).

(* The main test, with a non-empty list of bound variables. *)
global goal [bis] _ (tau:timestamp[param],i:index[param]) :
  [(forall (i0,i1:index), 
     diff(
     (A(i0) <= tau => n(i) <> <one,n(i1)>),
     (A(i0) <= tau => m(i) <> <one,n(i1)>))) = true] ->
  equiv(output@tau) ->
  equiv(output@tau, diff(h(n(i),k),h(m(i),k))).
Proof.
  intro H E.
  prf 1.

  rewrite H.
  rewrite if_true in 1; 1: auto.
  fresh 1; 1:auto.
  by apply E.
Qed.

