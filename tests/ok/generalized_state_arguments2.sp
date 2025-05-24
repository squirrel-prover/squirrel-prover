include Core.

name n : index -> message.

mutable s (i : index) = n i.

mutex l : 0.

abstract i0 : index.

channel c.

abstract toI : message -> index

name k : index * index -> message.

hash h.

(* -------------------------------------------------- *)
system Q = !_i lock l; in(c,x); s (toI (k (i, i0))) := empty; O: out(c,s (toI (k (i, i0)))); unlock l.

(* -------------------------------------------------- *)
(* check that [s] is well-formed *)
lemma [Q] _ (i, j : index) : 
  happens (O i) => 
  s j@O i = 
  if j = toI (k (i, i0)) then 
    empty 
  else 
    s(j)@pred (O(i)).
Proof.
  intro Hap.
  rewrite /s.
  apply eq_refl.
Qed.

lemma [Q] _ (j : index) : 
  s j@init = n j. 
Proof.
  rewrite /s.
  apply eq_refl.
Qed.
