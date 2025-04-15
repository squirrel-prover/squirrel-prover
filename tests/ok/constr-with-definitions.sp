include Core.

channel c.
system out(c,empty).

lemma  _  :
  let  t = A in
  let t'= A in
t=t'.
Proof.
intro E F.
constraints.
Qed.
