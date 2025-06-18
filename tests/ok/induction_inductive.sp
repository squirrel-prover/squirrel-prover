inductive tree a =
| leaf : tree a
| node : a -> tree a -> tree a -> tree a.

lemma _ @system:any ['a] (x : 'a) (t : tree 'a) p q:
  q t => p t.
Proof.
  intro H. 
  induction t.
  + by have ?: p leaf by admit.
  + intro a tl tg. by have ?: (p tg => p tl => p (node a tl tg)) by admit.
Qed.
