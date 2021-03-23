(*******************************************************************************
TOY EXAMPLE WITH STATE

System with tags only.

The goal is to prove the equivalence between:
- a system outputting the updated value kT(i) hashed with key(i) (ie same key for
all sessions of identity i),
- and a system outputting a fresh name at each session.

PROOFS
- lastUpdate
- stateInequality
- equivalence between real and ideal systems
*******************************************************************************)

hash hkey

abstract ok : message
abstract ko : message

name key : index->message
name seed : index->message
name n : index->index->message

mutable kT(i:index) : message = seed(i)

channel cT

process tag(i:index,j:index) =
  kT(i) := hkey(kT(i),key(i));
  out(cT, diff(kT(i),n(i,j)))

system (!_i !_j T: tag(i,j)).

(* GOALS *)

goal stateUpdate :
forall (t:timestamp), happens(t) =>
  (forall (i,j:index), t=T(i,j) => kT(i)@t = hkey(kT(i)@pred(t),key(i))).
Proof.
by auto.
Qed.

goal onlyTagActions :
forall (t:timestamp), happens(t) => (t <> init => exists (i,j:index), t=T(i,j)).
Proof.
intro t Hap Hneq.
case t. 
by exists i,j.
Qed.

goal notInit :
forall (t:timestamp), happens(t) =>
  ((exists (t':timestamp), t' < t)  => (t <> init)).
Proof.
by auto. 
Qed.

(* kT(i)@t = kT(i)@t' where t' is init or the previous update of kT(i) *)
goal lastUpdate : forall (t:timestamp) forall (i:index)
  happens(t) =>
  ((kT(i)@t = kT(i)@init && forall (j':index), happens(T(i,j')) => t < T(i,j')) ||
    (exists j:index,
     kT(i)@t = kT(i)@T(i,j) &&
     T(i,j) <= t &&
     (forall (j':index), happens(T(i,j')) => (T(i,j')<=T(i,j) || t<T(i,j'))))).
Proof.
induction.
case t.

(* t = init *)
left.

(* t = T(i1,j) *)
assert (i=i1 || i<>i1).
case H0.

(* t = T(i,j) *)
right; exists j.

(* t = T(i1,j) with i<>i1 *)
subst t,T(i1,j).
assert kT(i)@T(i1,j) = kT(i)@pred(T(i1,j)).
expand kT(i)@T(i1,j).
by noif.
use H with pred(T(i1,j)),i.
case H0.

  left.
  by use H0 with j'.

  right.
  exists j1.
  use H1 with j'.
  by case H0.
Qed.

goal stateInequality :
  forall (t:timestamp),
  (forall (t':timestamp), forall (i,j,i':index)
     happens(t) =>
     (t = T(i,j) && t' < t => kT(i)@t <> kT(i')@t')).
Proof.
induction.
subst t, T(i,j).
assert kT(i')@t' = hkey(kT(i)@pred(T(i,j)),key(i)).
euf Meq0.

(* T(i,j1) < T(i,j)
   kT(i)@pred(T(i,j1)) = kT(i)@pred(T(i,j))
   in order to use IH0 we need timestamps of the form T(i,_)
   but pred(_) has no reason to be of that form...
   this is where lastUpdate comes into play *)

use lastUpdate with pred(T(i,j)),i.
case H1.

(* kT(i)@pred(T(i,j)) = kT(i)@init
   this can actually happen only if tag i has not played from init to pred(T(i,j))
   but we know that T(i,j1) < T(i,j): absurd *)
by use H1 with j1; case H0.

(* kT(i)@pred(T(i,j)) = kT(i)@T(i,j2)
   then we should have that T(i,j1) <= T(i,j2) *)
assert (T(i,j1) <= T(i,j2)).
use H2 with j1. case H1. case H0. case H0.

by use H with T(i,j2),pred(T(i,j1)),i,j2,i.
Qed.

goal stateInequalityHelpful :
forall (i,j,j':index), 
  happens(T(i,j)) => 
    ( T(i,j')<T(i,j) => kT(i)@pred(T(i,j)) <> kT(i)@pred(T(i,j')) ).
Proof.
intro i j j' Hap Hlt Heq.
by use stateInequality with T(i,j),T(i,j'),i,j,i.
Qed.

equiv test.
Proof.
(* use prf, and reuse stateInequality *)
induction t.
expand frame@T(i,j). expand exec@T(i,j). expand cond@T(i,j).
fa 0.
fa 1. fa 1.
expand output@T(i,j). expand kT(i)@T(i,j).
prf 1. yesif 1.
use stateInequalityHelpful with i,j,j1.
fresh 1. yesif 1.
Qed.
