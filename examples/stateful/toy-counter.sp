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
- The goal is to prove that the secret s is never leaked because the B receives
  only hashes with old values of the counter.

SECURITY PROPERTIES
- monotonicity of the counter
- secrecy (as a reachability property)
*******************************************************************************)

set autoIntro = false.

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
abstract (~<) : message -> message -> boolean

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

axiom orderSucc (n:message): n ~< mySucc(n).

axiom orderTrans (n1,n2,n3:message): n1 ~< n2 && n2 ~< n3 => n1 ~< n3.

axiom orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 => false.

(* SECURITY PROPERTIES *)

(* The counter increases strictly at each update. *)
goal counterIncreasePred (t:timestamp): 
  t > init => d@pred(t) ~< d@t.
Proof.
  intro Hc. 
  use orderSucc with d@pred(t).
  case t; 2,3,4: auto. 
  constraints.
Qed.

(* A more general result than counterIncreasePred. *)
goal counterIncrease (t,t':timestamp):
   t' < t => d@t' ~< d@t.
Proof.
  induction t => t Hind Ht.
  assert (t' < pred(t) || t' >= pred(t)) as H0 by case t. 
  case H0.

    (* case t' < pred(t) *)
    apply Hind in H0 => //.
    use counterIncreasePred with t; 2: by constraints.
    by apply orderTrans _ (d@pred(t)).

    (* case t' >= pred(t) *)
    assert t' = pred(t) as Ceq by constraints.
    use counterIncreasePred with t; 2: auto.
    by rewrite Ceq; use counterIncreasePred with t.
Qed.

goal secretReach (j:index):
  happens(B(j)) => cond@B(j) => false.
Proof.
  intro Hap Hcond.
  expand cond.
  euf Hcond => Ht Heq. 
  assert pred(A(i)) < pred(B(j)) as H by constraints.
  apply counterIncrease in H.
  by apply orderStrict in H. 
Qed.
