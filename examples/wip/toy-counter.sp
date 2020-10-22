(*******************************************************************************
TOY-COUNTER

V. Cheval, V. Cortier, and M. Turuani,
‘A Little More Conversation, a Little Less Action, a Lot More Satisfaction:
Global States in ProVerif’,
in 2018 IEEE 31st Computer Security Foundations Symposium (CSF), Oxford,
Jul. 2018, pp. 344–358, doi: 10.1109/CSF.2018.00032.

A = in(d, i : nat); out(c, h(i, s)); out(d, i + 1)
B = in(d, i : nat); in(c, y);
    if y = h(i, s) then
      out(c, s); out(d, i + 1)
    else out(d, i + 1)

P = ! A | ! B | out(d, 0) | ! in(d, i : nat); out(d, i)
*******************************************************************************)

hash h

name secret : message
name key : message

abstract error : message

mutable d : message

channel cA
channel cB

(* initial value for counter *)
abstract myZero : message
axiom counterInit : d@init = myZero

(* myPred and mySucc functions for counter *)
abstract myPred : message->message
abstract mySucc : message->message
axiom predSucc : forall (n:message), myPred(mySucc(n)) = n

(* order relation for counter *)
abstract orderOk : message
abstract order : message->message->message
axiom orderSucc : forall (n:message), order(n,mySucc(n)) = orderOk
axiom orderTrans :
  forall (n1,n2,n3:message),
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
    => order(n1,n3) = orderOk
axiom orderStrict : forall (n1,n2:message), n1 = n2 => order(n1,n2) <> orderOk

(* processes *)
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
  forall (t:timestamp), t > init => order(d@pred(t),d@t) = orderOk.
Proof.
intros.
apply orderSucc to d@pred(t).
case t. case H0.
Qed.

goal counterIncreaseBis :
  forall (t:timestamp), forall (t':timestamp), t' < t => order(d@t',d@t) = orderOk.
Proof.
induction.
apply IH0 to pred(t).
assert (t' < pred(t) || t' >= pred(t)).
case H1.
(* case t' < pred(t) *)
apply H0 to t'.
apply counterIncrease to t.
apply orderTrans to d@t',d@pred(t),d@t.
(* case t' >= pred(t) *)
assert t' = pred(t).
apply counterIncrease to t.
Qed.

goal auth : forall (j:index), cond@B(j) => exists (i:index), A(i)<B(j) && input@B(j) = output@A(i).
Proof.
intros.
expand cond@B(j).
euf M0.
exists i.
case H0.
Qed.

goal secretReach : forall (j:index), cond@B(j) => False.
Proof.
intros.
expand cond@B(j).
euf M0.
apply predSucc to d@pred(A(i)).
apply predSucc to d@pred(B(j)).
assert d@pred(A(i)) = d@pred(B(j)).
assert pred(A(i)) < pred(B(j)). case H0.
apply counterIncreaseBis to pred(B(j)).
apply H1 to pred(A(i)).
apply orderStrict to d@pred(A(i)),d@pred(B(j)).
Qed.
