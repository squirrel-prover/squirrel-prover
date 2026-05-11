include "Data/List.sp".  

open List.

(* check that we can instantiate a polymorphic lemma *)
lemma length_rev_int @system:any (l : list int) :
    length (rev l) = length l.
Proof. apply length_rev. Qed.

(*------------------------------------------------------------------*)
let rec idf ['a] (x : 'a) : 'a = x.

lemma _ @system:any ['a] (x:'a) : idf x = x.
Proof. rewrite /idf. apply eq_refl. Qed.

(*------------------------------------------------------------------*)
let second ['a] (x,y:'a) = y.

axiom [any] _  : forall x:message, (second x x) = x.

