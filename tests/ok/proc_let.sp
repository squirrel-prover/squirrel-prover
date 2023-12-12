include Basic.

channel c.

process foo = 
  let x = true in O:out(c,empty).

process bar = 
  O: out(c,empty).

system [P] foo.
system [Q] bar.

lemma [P] _ : happens(O) => x@O = true.
Proof.
 intro H.
 rewrite /x.
 apply eq_refl.
Qed.

axiom [any] ax : witness = true.

lemma [Q] _ : happens(O) => x@O = true.
Proof.
 intro H.
 rewrite /x.
 apply ax.
Qed.
