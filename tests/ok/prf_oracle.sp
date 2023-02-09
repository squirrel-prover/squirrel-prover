

name leakedk:message

hash h with oracle forall (m:message,sk:message), sk=leakedk

name k:message

channel c
name n:message
name m:message
system null.

include Basic.

(* Test direct case *)
equiv test : h(diff(m,n),k),h(diff(n,m),k) .
Proof.
prf 1.

rewrite if_true. 
by project; auto.
fresh 1 => //.

prf 0.
by rewrite if_true.
Qed.
