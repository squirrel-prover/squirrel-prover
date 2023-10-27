include Basic.

lemma [any] rewrite_fun x :
let f = fun (x:message) => x in 
f (f x) = x.
Proof.
intro f.
rewrite /f.
by reduce.
Qed.

lemma [any] using_let_lemma (x:message):
(fun (x:message) => x) ((fun (x:message) => x) x) = x.
Proof.
apply rewrite_fun. 
Qed.
