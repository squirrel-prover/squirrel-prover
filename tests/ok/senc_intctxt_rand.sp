include Basic.

senc enc, dec.

name k : message.
name r : message.
name n : index -> message.

channel c.

system  A: out(c, seq(i : index => enc(n(i), r, k))).

axiom false_ax (i,i0:index) : n i = n i0.

lemma foo : happens(A) => dec(att(output@A),k) = fail. 
Proof. 
  intro ?.
  rewrite -not_neq => H.
  intctxt H. 
  + intro [i1 i2 H1].
    rewrite (false_ax i1 i2) in H1. 
    auto.
  + admit.
Qed.
