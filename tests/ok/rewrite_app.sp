(* test that rewriting sees [t1 t2 t3] as [(t1 t2) t3], and 
   in particular tries to rewriting the sub-term [(t1 t2)] *)

include Basic.

axiom [any] foo ['a 'b] f (g : _ -> 'b) (x : 'a) : f x = g x.

(* no problem here *)
lemma [any] _ ['a] (x : 'a) f (g : 'a -> 'a) (y : 'a) : 
  g x = y => f x = y.
Proof.
  intro H.
  rewrite (foo f g).
  assumption H.
Qed.

(* here, rewriting must consider decompositions of an application as sub-terms *)
lemma [any] _ ['a] (x,z : 'a) f (g : 'a -> 'a -> 'a) (y : 'a) : 
  g x z = y => f x z = y.
Proof.
  intro H.
  rewrite (foo f g).
  assumption H.
Qed.

(* idem *)
lemma [any] _ ['a 'b] (x,y : 'a -> 'a -> 'b) a b : 
(if true then x else y) a b = x a b. 
Proof.
  rewrite if_true //.
Qed. 
