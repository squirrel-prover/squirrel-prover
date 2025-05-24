type nat.
type key.

hash h where m: nat k:key h:message.
name k : key.

channel c.

(**
In order to model counter values, we use:
* a function `Succ` modelling the successor of a value;
* an order relation `~<` modelling the usual order on natural numbers.
* an abstract symbol `one` modelling the constant 1

We axiomatize the order relation `~<` defined above in order to be able
to reason on counter values.
*)

abstract one : nat
abstract Succ : nat->nat
abstract (~<) : nat -> nat-> boolean.

axiom [any] orderSucc (n:nat): n ~< Succ(n).
axiom [any] orderTrans (n1,n2,n3:nat): n1 ~< n2 && n2 ~< n3 => n1 ~< n3.
axiom [any] orderStrict (n1,n2:nat): n1 = n2 => not(n1 ~< n2).

include Real.

hint smt orderSucc.
hint smt orderTrans.
hint smt orderStrict.

mutable cpt : nat = one.

mutex l : 0.

process A =
  lock l;
  let m = h(cpt,k) in
  cpt := Succ(cpt);
  unlock l;
  out(c, m).

system ((!_i A)).

lemma counterIncrease (t,t':timestamp):
   t' < t => cpt@t' ~< cpt@t.
Proof.
induction t. smt ~steps:7833.
Qed.

lemma reach (tau:timestamp): input@tau <> h(cpt@tau,k).
Proof.
intro Eq; euf Eq. 
use counterIncrease; smt ~steps:5251.
Qed.

