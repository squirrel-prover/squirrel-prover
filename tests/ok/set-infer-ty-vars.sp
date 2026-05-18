include "Data/List.sp".

system null.

let rec map ['a 'b] (f : 'a -> 'b) (l : list 'a) : list 'b with
| Nil -> Nil
| Cons hd tl -> Cons (f hd) (map f tl).
Proof.
  intro > <-; discriminate.
Qed.

lemma _ (l : list message) (f : message -> message) l2 :
  map f l = l2.
Proof.
 set x := map _ _.
Abort.

lemma _ (l : list message) (f : message -> message) l2 :
  map f l = l2.
Proof.
 set x := map _ l.
Abort.

lemma _ (l : list message) (f : message -> message) l2 :
  map f l = l2.
Proof.
 set x := map f _.
Abort.
