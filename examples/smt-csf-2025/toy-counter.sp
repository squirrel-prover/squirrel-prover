hash h.
name key : message.

channel c.

(**
In order to model counter values, we use:
* a function `Succ` modelling the successor of a value;
* an order relation `~<` modelling the usual order on natural numbers.
* an abstract symbol `one` modelling the constant 1

We axiomatize the order relation `~<` defined above in order to be able
to reason on counter values.
*)

abstract one : message
abstract Succ : message->message
abstract (~<) : message -> message -> boolean.

axiom [any] orderSucc (n:message): n ~< Succ(n).
axiom [any] orderTrans (n1,n2,n3:message): n1 ~< n2 && n2 ~< n3 => n1 ~< n3.
axiom [any] orderStrict (n1,n2:message): n1 = n2 => not(n1 ~< n2).


mutable cpt : message = one.

process A =
  let m = h(cpt,key) in
  cpt := Succ(cpt);
  out(c, m).

system ((!_i A)).

lemma counterIncreasePred (t:timestamp):
  t > init => cpt@pred(t) ~< cpt@t.
Proof.
 intro Hc. 
 case t => //.
 use orderSucc with cpt@pred(t) => //.
Qed.

lemma counterIncrease (t,t':timestamp):
   t' < t => cpt@t' ~< cpt@t.
Proof.
induction t.
intro  t Hind Ht.
assert (t' < pred(t) || t' = pred(t)) as H0 => //.
use counterIncreasePred with t => //. 
case H0 => //.
use  Hind with pred(t) => //.  
by apply orderTrans _ (cpt@pred(t)).
Qed.

lemma reach (tau:timestamp): att(frame@tau) <> h(cpt@tau,key).
Proof.
intro Eq; euf Eq. 
 intro [i [H1 H2]].
assert (pred(A(i)) < tau) => //.
use counterIncrease with tau, pred(A(i)) => //.
use orderStrict with cpt@tau, cpt@pred(A(i)) => //.
Qed.

