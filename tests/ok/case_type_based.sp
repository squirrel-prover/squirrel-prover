channel c

system (in(c,x);out(c,x) | !_i in(c,x);out(c,x)).

lemma _ (t:timestamp) :
  t = init || (t = A || exists (i:index), t = A1(i)).
Proof.
  case t => _.  
  by left. 
  by right; left. 
  by right; right. 
Qed.

(*------------------------------------------------------------------*)
inductive t = L : t | R : int -> t.

lemma _ @system:any (t:t) :
  (t = L || exists (i:int), t = R i).
Proof.
  case t.
  + left; auto.
  + intro i; right; exists i; auto.
Qed.

(*------------------------------------------------------------------*)
inductive tree a =
| leaf : tree a
| node : a -> tree a -> tree a -> tree a.

lemma _ @system:any ['a] (x : 'a) (t : tree 'a) :
  t = leaf || exists a tl tg, t = node a tl tg.
Proof.
  case t.
  + by left.
  + by intro a tl tg; right; exists a, tl, tg.
Qed.
