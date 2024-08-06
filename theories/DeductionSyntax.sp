(* `Deduction` *)
predicate ( |> ) ['a 'b] {set} {set: (u : 'a, m : 'b)} =
  Exists (f : _[adv]), [f u = m].

(* `Deduction`, version with an argument to `u` and `m` 
   handled uniformly by `f`  *)
predicate ( |1> ) ['a 'b 'c] {set} {set: (u : 'a -> 'b, m : 'a -> 'c)} =
  Exists (f : _[adv]), [forall (x : 'a), f (u x) = m x].
