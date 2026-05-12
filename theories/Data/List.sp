include Logic.
include Int.
open Int.

(*------------------------------------------------------------------*)
inductive list a = 
| Nil : list a
| Cons : a -> list a -> list a.

(*------------------------------------------------------------------*)
namespace List.
  (* reverse [l2] and concatenate it with [l1] *)
  let rec append_rev ['a] (l1 : list 'a) (l2 : list 'a) : list 'a with
  | Nil -> l1
  | Cons a l2 -> append_rev (Cons a l1) l2.
  Proof.
    intro > <-; discriminate. 
  Qed.

  (*------------------------------------------------------------------*)
  (* reverse [l1] and concatenate it with [l2] *)
  let rev_append ['a] (l1 : list 'a) (l2 : list 'a) : list 'a =
    append_rev l2 l1.

  (*------------------------------------------------------------------*)
  let rev ['a] (l : list 'a) : list 'a = append_rev Nil l.

  (*------------------------------------------------------------------*)
  let append ['a] (l1 : list 'a) (l2 : list 'a) : list 'a =
    append_rev l1 (rev l2).

  (*------------------------------------------------------------------*)
  let rec length ['a] (x : list 'a) : int with
  | Nil -> 0
  | Cons _ l -> 1 + length l.
  Proof.
    intro > <-; discriminate. 
  Qed.

  (*------------------------------------------------------------------*)
  lemma length_nil @system:any ['a] :
    length Nil['a] = 0.
  Proof. rewrite /length; apply eq_refl. Qed. 

  lemma length_append_rev @system:any ['a] (l1,l2 : list 'a) :
    length (append_rev l1 l2) = length l1 + length l2.
  Proof. 
    generalize l1.
    induction l2.
    + auto.
    + intro > IH l1. 
      rewrite /append_rev IH /length. 
      set ? := length _.
      set ? := length _. 
      smt ~no_macros.
  Qed.

  lemma length_rev @system:any ['a] (l : list 'a) :
    length (rev l) = length l.
  Proof. by rewrite /rev length_append_rev. Qed.
end List.
