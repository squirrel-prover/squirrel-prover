set autoIntro=false.
(* set debugConstr=true. *)

hash h
name k:message
channel c
name n:message
name m:message
system null.

(* Test direct case *)
equiv test : h(diff(m,n),k),h(diff(n,m),k) .
Proof.
prf 1.

yesif 1.
by project.
fresh 1.

prf 0.
by yesif 0.
Qed.


system [test]
  in(c,x);
  let surp = diff(m,n) in
  let mac = h(<x,surp>,k) in
  out(c,mac);
  out(c,h(diff(<x,n>,<x,m>),k)).

equiv [test] test2.
Proof.

induction t.

auto.

expandall.
fa 0.
fa 1. fa 1. prf 1. 
(* easy case, it is the firt produced hash. *)
yesif 1.
by project.
by fresh 1.

expandall.
fa 0.
fa 1; fa 1.
prf 1.
yesif 1; simpl.
project.

(* Here, if the macros are not correclty projected, we cannot prove the goal,
else it is automatically simplified. *)
by split; intro H0; case H0; depends A, A1.
by split; intro H0; case H0; depends A, A1.

by fresh 1.
Qed.


system [failing]
  in(c,x);
  let key=x in
  let surp = diff(m,n) in
  let mac = h(k,key) in
  out(c,<mac, diff(m,n)>).

equiv [failing] testfail.
Proof.
induction t.

auto.

expandall.
fa 0; fa 1; fa 1; fa 1.
checkfail prf 1 exn BadSSC.
Abort.
