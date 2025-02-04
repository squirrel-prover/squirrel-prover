system null.

(*------------------------------------------------------------------*)
global lemma _ {P:system[pair]} @system:P (a,b,c1,c2 :bool) :
  (([c1] \/ [c1]) -> [a => b => c1 = c2]) ->
  [a => c1].
Proof.
  intro A.
  intro C.
  rewrite (A C). 
  + ghave H : [c1] \/ [c1] by admit. assumption H.
  + have H : b  by admit. assumption H.
  + have H : c2 by admit. assumption H.
Qed.

global lemma _ {P:system[pair]} @system:P (a,b,c1,c2 :bool) :
  (([c1] \/ [c1]) -> [a => b => c1 = c2]) ->
  [a => c1].
Proof.
  intro A.
  intro C.
  rewrite (A _ C). 
  + ghave H : [c1] \/ [c1] by admit. assumption H.
  + have H : b  by admit. assumption H.
  + have H : c2 by admit. assumption H.
Qed.

(*------------------------------------------------------------------*)
global lemma _ {P:system[pair]} @equiv:P @set:P (a : int -> bool) (b,c1,c2 :bool) :
   (Forall(x : int), [ a x => c1 = c2 ]) -> [c2] -> [a 42 => c1].
Proof.
  intro A H. intro C.
  rewrite (A C). 
  assumption H.
Qed.
