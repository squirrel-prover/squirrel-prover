set autoIntro=false.

channel ch
abstract ok : message

abstract a : message
abstract b : message
abstract c : message
abstract d : message

system A: if True then out(ch,ok).

axiom fooa : a = b => False.
axiom foob : b = c => False.

goal foo : forall (i : index, l : index, j : index),
 (a = b || (b = c && c = d)) => False.

Proof.
 intro _ _ _ [H | [H G]]. 
 by use fooa.
 by use foob.
Qed.
