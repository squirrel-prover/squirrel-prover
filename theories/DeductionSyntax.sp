(* `Deduction`
   `'a` and `'b` must be order 0 or 1 types. *)
predicate ( |> ) ['a 'b] {set : system} {set: (u : 'a, m : 'b)} =
  Exists (f : 'a -> 'b[adv]), [f u = m].

(*------------------------------------------------------------------*)
(* Variant of `Deduction` where:
   - `u` and `m` are order-1;
   - `f` is uniform w.r.t. `u` and `m`
   - we require that deduction holds exactly.

   Remark that `'b` and `'c` must be order 0 or 1 types. *)
predicate ( |1> ) ['a 'b 'c] {set : system} {set: (u : 'a -> 'b, m : 'a -> 'c)} =
  Exists (f : 'b -> 'c[adv]), [forall (x : 'a), f (u x) = m x <: Real.z].
