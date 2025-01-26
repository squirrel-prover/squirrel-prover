include Core.

(*------------------------------------------------------------------*)
op g : message -> message.

lemma [any] rewrite_fun x :
let f = g in 
f (g x) = x.
Proof.
intro f.
rewrite /f.
admit.
Qed.

lemma [any] using_let_lemma (x:message):
g (g x) = x.
Proof.
apply rewrite_fun. 
Qed.
