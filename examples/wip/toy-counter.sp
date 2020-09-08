(*******************************************************************************
TOY-COUNTER

V. Cheval, V. Cortier, and M. Turuani, 
‘A Little More Conversation, a Little Less Action, a Lot More Satisfaction: 
Global States in ProVerif’, 
in 2018 IEEE 31st Computer Security Foundations Symposium (CSF), Oxford, 
Jul. 2018, pp. 344–358, doi: 10.1109/CSF.2018.00032.
*******************************************************************************)

hash h

name secret : message
name key : message

abstract error : message

mutable d : message

channel cA
channel cB

abstract myZero : message
abstract myPred : message->message
abstract mySucc : message->message

axiom counterInit : d@init = myZero
axiom predSucc : forall (n:message), myPred(mySucc(n)) = n
axiom succPred : forall (n:message), mySucc(myPred(n)) = n
axiom notEqual : forall (n:message), n <> mySucc(n)

process A =
  d := mySucc(d);
  out(cA, h(<myPred(d),secret>,key))

process B =
  in(cA,y);
  if y = h(<myPred(d),secret>,key) then
    d := mySucc(d);
    out(cB,secret)
  else
    d := mySucc(d);
    out(cB,error)

system ((!_i A) | (!_j B)).

goal counterIncrease :
  forall (t:timestamp), t > init => d@t = mySucc(d@pred(t)). 
Proof.
intros.
case t. case H0.
Qed.

goal counterIncreaseBis :
  forall (t:timestamp), forall (t':timestamp), t' < t => d@t <> d@t'.
Proof.
induction.
apply IH0 to pred(t).
assert (t' < pred(t) || t' >= pred(t)).
case H1.

apply counterIncrease to t.
apply notEqual to d@pred(t).
apply H0 to t'.
assert d@pred(t) <> d@t.
(* TODO *) admit.
(* axiom notEqual me semble pas suffisant *)

assert t' = pred(t).
apply counterIncrease to t.
apply notEqual to d@t'.
Qed.

goal auth : forall (j:index), cond@B(j) => exists (i:index), A(i)<B(j) && input@B(j) = output@A(i).
Proof.
intros.
expand cond@B(j).
apply predSucc to d@pred(B(j)).
assert input@B(j) = h(<d@pred(B(j)),secret>,key).
euf M2.
exists i.
Qed.

goal secretReach : forall (j:index), cond@B(j) => False.
Proof.
intros.
expand cond@B(j).
apply predSucc to d@pred(B(j)).
assert input@B(j) = h(<d@pred(B(j)),secret>,key).
euf M2.
apply predSucc to d@pred(A(i)).
assert <d@pred(A(i)),secret> = <d@pred(B(j)),secret>.
assert d@pred(A(i))=d@pred(B(j)).
assert (A(i)=pred(B(j)) || A(i)<pred(B(j))).
case H0.

assert d@A(i) = d@pred(A(i)).
apply notEqual to d@pred(A(i)).

(* TODO *) admit.
Qed.
