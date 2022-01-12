
(* REM *)
(* some random tests *)
op P : int -> bool.
op Q : int -> bool.

lemma foo (a b : int) : 
    (forall (x : int), P x) =>
    (forall (y : int), P y => Q y) => false. 
proof.
  move => H G.
  have V := G (_+_) (H (1 + 1)).
  have V' := G (1+1) (H (_ + _)).

lemma foo ['a] (x, y : 'a) : 
    (forall (z : 'a), x = z => (x,z) = (z,x)) => 
    (forall (u : int), x = y) => y = x.
proof.
  move => H U.
  have V := H _ (U).
