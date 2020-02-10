(** This example tries to illustrate the difficulty about happens.  Both actions
should never happen. We should be able to prove not(happen(A)).  We might have
use happen too often, as it implies the condition of the action, and may
trivialize some proofs. *)

hash h

abstract ok:message
abstract ko:message

name k : message
name l : message

channel c
channel d

process A =
in(c,x);
if x=h(ok,k) then
out(c,h(ok,l))
else out(c,ko)

process B =
in(d,x);
if x=h(ok,l) then
  out(d,h(ok,k))
else
   out(d,ko)
system (A | B).


goal triv:
forall tau:timestamp,
happens(tau)  =>
  (input@tau = h(ok,k) || input@tau = h(ok,k)).
   Proof.
   admit.
 Qed.

goal not_happens:
forall tau:timestamp,
(tau = A || tau = B)  =>
  not(input@tau = h(ok,k)) &&  not(input@tau = h(ok,k)).
 Proof.
induction.
intros.
split.
 case H0.
  euf M0.
