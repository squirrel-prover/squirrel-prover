channel ch
abstract ok : message

abstract a : message
abstract b : message
abstract c : message
abstract d : message

system A: if true then out(ch,ok).

axiom fooa : a = b => false.
axiom foob : b = c => false.

lemma _ (i : index, l : index, j : index):
 (a = b || (b = c && c = d)) => false.

Proof.
 intro [H | [H G]]. 
 by use fooa.
 by use foob.
Qed.

lemma _ (i : index, j: index, k : index) :
  (exists (l : index), false) => false.
Proof.
 intro [l _]; auto.
Qed.

lemma _ (i : index, j: index, k : index) :
  (exists (l : index), true) => false.
Proof.
 intro [l _].
 admit.
Qed.

lemma _ (i : index, j: index, k : index) :
  (exists (i, l, l1, l2, l3 : index), true) => false.
Proof.
 intro [l2 l3 l4 Hap]. 
 admit.
Qed.

lemma _ (i : index, j: index, k : index) :
  (false || false || false) => false.
Proof.
 intro [_|_|_]; assumption.
Qed.

lemma _ (i : index, j: index, k : index) :
  (((a = b && a = c && c = d) => a = b) &&
   ((a = b && a = c && c = d) => a = c) &&
   ((a = b && a = c && c = d) => c = d)).
Proof.
 split;
 2: split.
 intro [_ _ _]; assumption.
 intro [_ _ _]; assumption.
 intro [_ _ _]; assumption.
Qed.

(*------------------------------------------------------------------*)

op foo x y = <x,y>.
op (+*) x y = <x,y>.

lemma _ x y : x +* y = foo x y.
Proof.
  intro @/foo @/( +* ).
  auto.
Qed.
