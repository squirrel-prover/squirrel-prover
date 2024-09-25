(* `Deduction`
   `'a` and `'b` must be order 0 or 1 types. *)
predicate ( |> ) ['a 'b] {set : system} {set: (u : 'a, m : 'b)} =
  Exists (f : 'a -> 'b[adv]), [f u = m].
(* TODO: quantum: it should be the exact reachability predicate, 
   not the overwhelming one *)

(* `Deduction`, version with an argument to `u` and `m` 
   handled uniformly by `f`.
   `'b` and `'c` must be order 0 or 1 types. *)
predicate ( |1> ) ['a 'b 'c] {set : system} {set: (u : 'a -> 'b, m : 'a -> 'c)} =
  Exists (f : 'b -> 'c[adv]), [forall (x : 'a), f (u x) = m x].
(* TODO: quantum: it should be the exact reachability predicate, 
   not the overwhelming one *)
