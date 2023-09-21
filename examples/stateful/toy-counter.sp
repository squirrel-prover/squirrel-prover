(**
# TOY-COUNTER

V. Cheval, V. Cortier, and M. Turuani,  
*A Little More Conversation, a Little Less Action, a Lot More Satisfaction:
Global States in ProVerif*,  
in 2018 IEEE 31st Computer Security Foundations Symposium (CSF), Oxford,
Jul. 2018, pp. 344–358,  
doi: 10.1109/CSF.2018.00032.

* `A = in(d, i : nat); out(c, h(i, s)); out(d, i + 1)`
* `B = in(d, i : nat); in(c, y);`  
  `if y = h(i, s) then`  
  `out(c, s); out(d, i + 1)`  
  `else`  
  `out(d, i + 1)`
* `P = ! A | ! B | out(d, 0) | ! in(d, i : nat); out(d, i)`

#### COMMENTS

- In this model, we do not use private channels since actions (input/condition/
  update/output) are atomic.
- The goal is to prove that the secret s is never leaked because B receives
  only hashes with old values of the counter.

#### SECURITY PROPERTIES

- monotonicity of the counter
- secrecy (as a reachability property)
*)

hash h

name secret : message
name key : message

abstract error : message
abstract myZero : message

(** We declare here a mutable state symbol, initialized with the public constant
`myZero`. *)
mutable d : message = myZero

channel cA
channel cB.

(**
In order to model counter values, we use:

* a function `mySucc` modelling the successor of a value;
* an order relation `~<` modelling the usual order on natural numbers.

*)
abstract mySucc : message->message
abstract (~<) : message -> message -> boolean.

(** Processes A and B are defined as follows.
They both access to the mutable state `d`. *)
process A =
  let m = h(<d,secret>,key) in
  d := mySucc(d);
  out(cA, m).

process B =
  in(cA,y);
  if y = h(<d,secret>,key) then
    d := mySucc(d);
    out(cB,secret)
  else
    d := mySucc(d);
    out(cB,error).

system ((!_i A) | (!_j B)).

(**
#### AXIOMS

We now axiomatize the order relation `~<` defined above in order to be able
to reason on counter values.
*)
axiom orderSucc (n:message): n ~< mySucc(n).
axiom orderTrans (n1,n2,n3:message): n1 ~< n2 && n2 ~< n3 => n1 ~< n3.
axiom orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 => false.

(**
#### SECURITY PROPERTIES

We first show that the counter increases strictly at each update.
*)
lemma counterIncreasePred (t:timestamp):
  t > init => d@pred(t) ~< d@t.
Proof.
  intro Hc.
  use orderSucc with d@pred(t).
  case t => //.
Qed.

(**
We also show a more general result than counterIncreasePred, stating
here that the counter strictly increases between two distinct timestamps.

The proof is done by induction, and relies on the previous result
counterIncreasePred.
*)
lemma counterIncrease (t,t':timestamp):
   t' < t => d@t' ~< d@t.
Proof.
  induction t => t Hind Ht.
(** We use the `assert` tactic to introduce two cases. *)
  assert (t' < pred(t) || t' >= pred(t)) as H0 by case t.
  case H0.

       (** **Case where t' < pred(t):**
       We first apply the induction hypothesis on `t'` to get `d@t' ~< d@pred(t)`,
       then use the lemma counterIncreasePred with `t` to get `d@pred(t) ~< d@t`.
       It then remains to conclude by transitivity (applying `orderTrans`).
       *)
    +  apply Hind in H0 => //.
       use counterIncreasePred with t; 2: by constraints.
       by apply orderTrans _ (d@pred(t)).

       (** **Case where t' >= pred(t).**
       Since `t' < t` we can deduce that `t' = pred(t)`. It is then directly
       a consequence of the counterIncreasePred lemma.
       *)
    +  assert t' = pred(t) as Ceq by constraints.
       use counterIncreasePred with t; 2: auto.
       by rewrite Ceq; auto.
Qed.

(**
The following reachability property states that the secret s is never leaked
(_i.e._ the condition of the action `B(j)` is never satisfied).

The proof relies on the EUF assumption: if `cond@B(j)` is satisfied, it would
mean that the attacker has been able to forge the message `h(<d,secret>,key)`
with `d` corresponding to the value of the counter at timepoint `B(j)`, because
all messages outputted so far correspond to older values of `d`.
*)
lemma secretReach (j:index):
  happens(B(j)) => cond@B(j) => false.
Proof.
  (** We start by introducing the hypotheses and expanding the `cond` macro. *)
  intro Hap Hcond.
  expand cond.
  (** Applying the `euf` tactic generates two new hypotheses, `Ht` and `Heq`. *)
  euf Hcond => [i [Ht Heq]].
  (** We use here the counterIncrease lemma to show that the equality `Heq` is
  not possible. *)
  assert pred(A(i)) < pred(B(j)) as H by constraints.
  apply counterIncrease in H.
  by apply orderStrict in H.
Qed.
