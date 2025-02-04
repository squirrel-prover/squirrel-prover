include Real. 
open Real.

global axiom foo @system:any : Forall b, [false <: b + of_int 10].

global lemma _ @system:any (b : Real.t) : [false <: of_int 1].
Proof.
  simpl.
  have A /= := localize(foo (of_int 100)).
  weak z; 2:auto.
  have B : z <=  opp (of_int (109)) by admit. 
  revert B; reduce => B.
  assumption B.
Qed.
