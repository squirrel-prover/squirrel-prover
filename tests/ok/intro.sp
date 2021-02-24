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

goal _ (i : index, l : index, j : index):
 (a = b || (b = c && c = d)) => False.

Proof.
 intro _ _ _ [H | [H G]]. 
 by use fooa.
 by use foob.
Qed.

goal _ (i : index, j: index, k : index) :
  (exists (l : index), False) => False.
Proof.
 intro i j k [l _]; auto.
Qed.

goal _ (i : index, j: index, k : index) :
  (exists (l : index), True) => False.
Proof.
 intro i j k [l _].
 admit.
Qed.
