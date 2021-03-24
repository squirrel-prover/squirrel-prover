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

COMMENTS
- In this model, we do not use private channels since actions (input/condition/
   update/output) are atomic.

PROOFS
- monotonicity of the counter
- secrecy (as a reachability property)
*******************************************************************************)

hash h

name secret : message
name key : message

abstract error : message
abstract myZero : message

mutable d : message = myZero

channel cA
channel cB

(* mySucc function for counter *)
abstract mySucc : message->message

(* order relation for counter *)
abstract orderOk : message
abstract order : message->message->message

(* processes *)
process A =
  let m = h(<d,secret>,key) in
  d := mySucc(d);
  out(cA, m)

process B =
  in(cA,y);
  if y = h(<d,secret>,key) then
    d := mySucc(d);
    out(cB,secret)
  else
    d := mySucc(d);
    out(cB,error)

system ((!_i A) | (!_j B)).

(* AXIOMS *)

axiom orderSucc : forall (n:message), order(n,mySucc(n)) = orderOk.
axiom orderTrans :
  forall (n1,n2,n3:message),
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
    => order(n1,n3) = orderOk.
axiom orderStrict : forall (n1,n2:message), n1 = n2 => order(n1,n2) <> orderOk.

(* GOALS *)

goal counterIncrease :
  forall (t:timestamp), happens(t) => 
    (t > init => order(d@pred(t),d@t) = orderOk).
Proof.
intro t Hap Hc.
use orderSucc with d@pred(t).
case t. 
Qed.

(* A more general result than counterIncrease *)
goal counterIncreaseBis :
  forall (t,t':timestamp), 
    (t' < t => order(d@t',d@t) = orderOk).
Proof.
induction.
assert (t' < pred(t) || t' >= pred(t)); 1: by case t. 
case H0.
use H with pred(t),t'.
(* case t' < pred(t) *)
use counterIncrease with t.
by use orderTrans with d@t',d@pred(t),d@t.
(* case t' >= pred(t) *)
assert t' = pred(t).
by use counterIncrease with t.
Qed.

goal secretReach : forall (j:index), happens(B(j)) => (cond@B(j) => False).
Proof.
intro *.
expand cond@B(j).
euf H.
assert pred(A(i)) < pred(B(j)).
use counterIncreaseBis with pred(B(j)),pred(A(i)).
use orderStrict with d@pred(A(i)),d@pred(B(j)).
Qed.
