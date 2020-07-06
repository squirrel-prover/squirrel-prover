(*******************************************************************************
TOY EXAMPLE WITH STATE
*******************************************************************************)

hash hkey

abstract seed : index->message
abstract ok : message
abstract ko : message

name key : index->index->message

mutable kT : index->message

channel cT

axiom stateInit :
  forall (i:index), kT(i)@init = seed(i)

process tag(i:index,j:index) =
  kT(i) := hkey(kT(i),key(i,j));
  out(cT, kT(i))

system (!_i !_j T: tag(i,j)).

goal state1 :
forall (t:timestamp), (forall (i,j:index), t=T(i,j) => kT(i)@t = hkey(kT(i)@pred(t),key(i,j))).
Proof.
induction.
Qed.

goal state2 :
forall (t:timestamp), (forall (i,j:index), t=T(i,j) => kT(i)@t <> kT(i)@pred(t)).
Proof.
induction.
assert kT(i)@pred(T(i,j)) = hkey(kT(i)@pred(T(i,j)),key(i,j)).
euf M3.
Qed.

equiv test.
Proof.
induction t.
expandall.
fa 0.
fa 1. fa 1.
prf 1. yesif 1.
fresh 1.
Qed.
