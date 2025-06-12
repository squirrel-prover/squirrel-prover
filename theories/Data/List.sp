include Logic.
include Int.
open Int.

(*------------------------------------------------------------------*)
inductive list a = 
| Nil : list a
| Cons : a -> list a -> list a.

(*------------------------------------------------------------------*)
namespace List.
  let rec length ['a] (x : list 'a) : int with
  | Nil -> 0
  | Cons _ l -> 1 + length l.
  Proof.
    intro > <-; discriminate. 
  Qed.

  lemma length_nil @system:any ['a] :
    length Nil = 0.
  Proof. rewrite /length; apply eq_refl. Qed. 
end List.
