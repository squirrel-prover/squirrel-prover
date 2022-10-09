
set postQuantumSound=true.

hash h
name sk : message
channel c

name k :  message

name ok : message
name ko : message

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



system [attT]
 (out(c, h(k,sk)); in(c,x); if snd(x) = h(fst(x),sk) && not(fst(x)=k) then O : out(c,diff(ok,ko)) else out(c,ok)).


global goal [attT] _  :
 [happens(O)] -> equiv(diff(cond@O,False)).
Proof.
  checkfail intro t exn GoalNotPQSound.
Abort.



global goal [attT] _  :
 [happens(O)] -> equiv(frame@pred(O))-> equiv(frame@pred(O), diff(cond@O, False)).
Proof.
  intro t Ind.
  have ->: cond@O <=> false. {
    expand cond.
    simpl.
    intro eq1.
    destruct eq1 as [P N].
    euf P.
    intro [ts eq].
    by depends A2,O.
  }

  auto.
Qed.
