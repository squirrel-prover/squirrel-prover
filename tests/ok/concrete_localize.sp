global lemma [any] _ (A : bool) : [A <: Real.z] -> [A <: Real.z].
Proof.
intro H.
localize H as HL. (* check that localize succeed without importing `Real` *)
Abort.

(*------------------------------------------------------------------*)
include Real. open Real.

global lemma [any] _ (A : bool) b1 b2 : 
  [b1 - b2 = z <: z] -> [A <: b2] -> [A <: b1].
Proof.
intro A H.
localize H as HL. 
rewrite A.
assumption HL.
Qed.

