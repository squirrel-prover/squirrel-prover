set autoIntro=false.

hash h

name key : message
name seed : message

mutable kT : message = seed

channel c

process tag(j:index) =
  T: out(c, h(kT,key)).

system !_j tag(j).

axiom no_repeat (i, j:timestamp): i < j => kT@j <> kT@i.

global goal foo (t: timestamp) :
  [forall (j, j0:index), (T(j0) < T(j) => kT@pred(T(j)) <> kT@T(j0))] ->
  [happens(t)] ->
  equiv(frame@t).
Proof.
intro H.
induction t.

(* t = init *)
by intro *.

(* t = T(j) *)
intro H1.
expandall.

fa 0.
fa 1.
fa 1.
prf 1. 
yesif 1; simpl.
by intro > _; apply H. 
fresh 1. 
admit 0.
auto.
Qed.
