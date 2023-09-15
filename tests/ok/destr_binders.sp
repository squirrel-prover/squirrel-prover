type T.

op fst_p = fun ((x,y) : T * T) => x.

axiom [any] foo : forall ((x,y) : T * T), x = y.
print foo.

lemma [any] _ (x, y : T) : x = y.
Proof.
  remember (x,y) as t => H.
  have ?:= foo t. 
  by rewrite H /= in Meq. 
Qed.

axiom [any] bar : exists ((x,y) : T * T), x = y.
print bar.

lemma [any] _ (x, y : T) : exists (x,y : T), x = y.
Proof.
  have [u H] := bar. 
  by exists u#1, u#2.
Qed.
