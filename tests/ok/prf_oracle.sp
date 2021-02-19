set autoIntro=false.

name leakedk:message

hash h with oracle forall (m:message,sk:message), sk=leakedk

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
by project; auto.
fresh 1.

prf 0.
yesif 0. 
by auto.
Qed.


system [test]  in(c,x); let surp = diff(m,n) in let mac = h(<x,surp>,k) in  out(c,mac); out(c,h(diff(<x,n>,<x,m>),k)).

equiv [left,test] [right,test] test2.
Proof.

induction t.
expandall.
fa 0; fa 1; fa 1. 
prf 1.
(* easy case, it is the firt produced hash. *)
yesif 1.
by project; auto.
by fresh 1.

expandall.
fa 0; fa 1; fa 1. 
prf 1. 
yesif 1. 
project.

(* Here, if the macros are not correclty projected, we cannot prove the goal,
else it is automatically simplified. *)
split; 1: by auto. 
by split; intro H0; case H0; depends A, A1; auto. 

split; 1: by auto. 
by split; intro H0; case H0; depends A, A1; auto. 

fresh 1.
Qed.
