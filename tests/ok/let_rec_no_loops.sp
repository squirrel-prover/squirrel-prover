include Core.
include "Data/List.sp".
include Int.
open Int.

(* We admit_adv, so that we can do a function over n and use crypto over it. *)
let rec zeros ~admit_adv (n:int) = if n=0 then Nil else Cons 0 (zeros (n-1)).
Proof.
smt.
Qed.

global lemma [any] ded_zero : $( () |> (zeros 0)).
Proof.
rewrite /zeros.
rewrite if_true //.
deduce. 
Qed.

global lemma [any] ded : Forall (n:_[const]), $( () |> (zeros n)).
Proof.
induction.
intro n IH.
ghave [C | C] : [n=0 || n <>0] by auto.
 - rewrite C. deduce with ded_zero.
 - expand (zeros n). 
   rewrite (if_false (n=0)) // /=.

   deduce with (IH (n-1)).
   smt. 
Qed.

let rec zeros_not_ptime (n:int) = if n=0 then Nil else Cons 0 (zeros_not_ptime (n-1)).
Proof.
smt.
Qed.

global lemma [any] _ : Forall (n:_[const]), 
$( (zeros_not_ptime (n-1)) |> (zeros_not_ptime n)).
Proof.
intro n.
deduce ~all. 
Qed.

game empty = {}.

name k:message.
name k2:message.

system null.

global lemma ded_zero_fresh : equiv(zeros 0, diff(k,k2)).
Proof.
 fresh 1. by assumption. 
 crypto empty.
Qed.


let rec zeros'  (n:timestamp) = if n=init || not(happens(n)) then (Cons k Nil) else Cons zero (zeros' (pred(n))).
Proof.
smt.
Qed.

global lemma ded_zero_fresh' (ts:timestamp [const]) : equiv(zeros' ts, diff(k,k2)).
Proof.
 fresh 1. 
 + have F : forall (t:timestamp), t <= ts => t = init || not( happens(t)) => false by admit.
   assumption F.
 + crypto empty.
Qed.

game Fresh = {
rnd n1:message;
rnd n2:message;

oracle t  = {
  return diff(n1,n2)
}
}.

global lemma ded_zero_fresh'' (ts:timestamp [const]) : equiv(zeros' ts, diff(k,k2)).
Proof.
 crypto Fresh (n1:k) (n2:k2).
 + have F : forall (t:timestamp), (t = init || not( happens(t))) && t <= ts => false   by admit.
  assumption F.
Qed.


let rec zeros_ts  t = if t=init || not(happens(t)) then Nil else Cons 0 (zeros_ts (pred t)).
Proof.
smt.
Qed.


global lemma [any] _ : Forall (t:_[const]), $( (zeros_ts (pred(pred(t)))) |> (zeros_ts t)).
Proof.
intro n.
checkfail (deduce ~all) exn ApplyMatchFailure. 
Abort.

set deduceUnrollOpaque=2.

global lemma [any] _ : Forall (t:_[const]), $( (zeros_ts (pred(pred(t)))) |> (zeros_ts t)).
Proof.
intro n.
deduce ~all. 
Qed. 

global lemma [any] _ : Forall (t:_[const]), $( (zeros_ts (pred(pred(pred(t))))) |> (zeros_ts t)).
Proof.
intro n.
checkfail (deduce ~all) exn ApplyMatchFailure. 
Abort.
