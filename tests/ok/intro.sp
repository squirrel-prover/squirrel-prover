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
 intro [H | [H G]]. 
 by use fooa.
 by use foob.
Qed.

goal _ (i : index, j: index, k : index) :
  (exists (l : index), False) => False.
Proof.
 intro [l _]; auto.
Qed.

goal _ (i : index, j: index, k : index) :
  (exists (l : index), True) => False.
Proof.
 intro [l _].
 admit.
Qed.

goal _ (i : index, j: index, k : index) :
  (exists (i, l, l1, l2, l3 : index), True) => False.
Proof.
 intro [l2 l3 l4 Hap]. 
 admit.
Qed.

goal _ (i : index, j: index, k : index) :
  (False || False || False) => False.
Proof.
 intro [_|_|_]; assumption.
Qed.

goal _ (i : index, j: index, k : index) :
  (((a = b && a = c && c = d) => a = b) &&
   ((a = b && a = c && c = d) => a = c) &&
   ((a = b && a = c && c = d) => c = d)).
Proof.
 split;
 1: split.
 intro [_ _ _]; assumption.
 intro [_ _ _]; assumption.
 intro [_ _ _]; assumption.
Qed.



