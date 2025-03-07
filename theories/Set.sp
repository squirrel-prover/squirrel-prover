type mset.

abstract empty_set : mset.

abstract mem : message -> mset -> bool.

abstract add : message -> mset -> mset.

op singleton (m : message) = add m empty_set.

(* Folding over a set, in an unspecified order for now. 
   FIXME: axiomatize or make concrete *)
op fold ['a] (f : message -> 'a -> 'a) (acc : 'a) (t : mset) : 'a.

(* `s1 ∪ s2` *)
op union (s1 : mset) (s2 : mset) : mset =
  fold (fun t s => add t s) s1 s2.

(* `s1 ⊆ s2` *)
op subseteq (s1 : mset) (s2 : mset) : bool =
  fold (fun t b => b && mem t s2) true s1.

axiom [any] empty_set_is_empty (x:message) : not (mem x empty_set).
