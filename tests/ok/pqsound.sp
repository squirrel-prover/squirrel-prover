set autoIntro=false.
set postQuantumSound=true.

hash h
channel c

name k : index -> message

name ok : message
name ko : message

ddh g, (^) where group:message exposants:message.

name a : message

name b : message

name d : message

system
!_i (if False then out(c,diff(ok,ko)) else out(c,ok)).

global goal _ (i:index) :
 [happens(A(i))] -> equiv(diff(cond@A(i),False)).
Proof.
  checkfail intro t exn GoalNotPQSound.
Abort.

global goal _ (i:index) :
 [happens(A(i))] -> equiv(frame@pred(A(i)))-> equiv(frame@pred(A(i)), diff(cond@A(i),False)).
Proof.
  intro t Ind.
  expand cond.
  auto.
Qed.
