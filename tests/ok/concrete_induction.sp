include Real.
open Real.

system null.

op bnd['a] : 'a -> Real.t.

global lemma _ (t : timestamp) (p:timestamp -> bool): [p t <: bnd t].
Proof.
  induction ~concrete t.
  intro t IH. 
  ghave ? /= : 
    Forall (t0:timestamp), [t0 < t <: z] -> [p t0 <: bnd t0] 
  by assumption IH. 
Abort.

inductive ty = L : ty | R : ty.

global lemma _ (x : ty) (p:ty -> bool): [p x <: bnd x].
Proof.
  (* FEAT: concrete: we could add a specific rule for concrete
     induction over indutive data-types. Until then, we can make do
     with the general induction rule. *)
  checkfail induction ~concrete x exn Failure. 
  induction ~concrete ~general x.
  intro x IH. 
  ghave ? /= : 
    Forall (x0:_), [x0 < x <: z] -> [p x0 <: bnd x0] 
  by assumption IH. 
Abort.
