

name leakedk:message

hash h with oracle forall (m:message,sk:message), sk=leakedk

name k:message

channel c
name n:message
name m:message

system  in(c,x); let surp = diff(m,n) in let mac = h(<x,surp>,k) in  out(c,mac); out(c,h(diff(<x,n>,<x,m>),k)).

include Basic.

equiv test2.
Proof.

induction t; try auto.
expandall.
fa 0; fa 1; fa 1. 
prf 1 => //.
(* easy case, it is the first produced hash. *)
by fresh 1.

expandall.
fa 0; fa 1; fa 1. 
prf 1 => //. 

by intro H0; depends A, A1. 
by fresh 1.
Qed.
