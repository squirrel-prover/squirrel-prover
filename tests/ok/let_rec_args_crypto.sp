include Core.
include "Data/List.sp".

name k:message.
name k2:message.

abstract tutu : index -> message.
mutable t (i:index) : message = tutu(i).

channel c
system !_i out(c,zero).




game Fresh = {
rnd n1:message;
rnd n2:message;

oracle t  = {
  return diff(n1,n2)
}
}.

game Empty = {}.

set debugMacros=true.

global lemma _ (ts : _ [const]) (i,j:index [const]) : 
equiv( t diff(i,j) @ ts).
Proof.
crypto Empty.
checkfail assumption exn NotHypothesis.
have _ : not(init <= ts) || not(true) by admit.
assumption.
Qed.


let rec zeros'' i  (n:timestamp) = if n=init || not(happens(n)) then (Cons i Nil) else Cons zero (zeros'' i (pred(n))).
Proof.
smt.
Qed.



global lemma _ (ts:timestamp [const]) : equiv(zeros'' diff(k,k2) ts,k).
Proof.
 crypto Fresh (n1:k) (n2:k2).
 checkfail assumption exn NotHypothesis.
Abort.

global lemma _ (ts:timestamp [const]) : equiv(zeros'' diff(k,k2) ts,k).
Proof.
 fresh 1. 
 + checkfail assumption exn NotHypothesis. 
   have _ : forall (t:timestamp), t <= ts => t = init || not(happens(t)) => false  by admit. 
   assumption.
 + admit.
Qed.


global lemma _ (ts:timestamp [const]) : equiv(zeros'' k ts,diff(k,k2)).
Proof.
 fresh 1. 
 + checkfail assumption exn NotHypothesis. 
   have _ : forall (t:timestamp), t <= ts => t = init || not(happens(t)) => false  by admit.
   assumption.
 + crypto Empty.   
Qed.

global lemma _ (ts:timestamp [const]) : equiv(zeros'' k ts,diff(k,k2)).
Proof.
 crypto Fresh (n1:k) (n2:k2).
 checkfail assumption exn NotHypothesis.
 have _ : forall (t:timestamp), (t = init || not(happens(t))) && t <= ts => false by admit.
 assumption.
Qed.
