(*******************************************************************************
TOY EXAMPLE WITH STATE

System with tags only.

The goal is to prove the equivalence between:
- a system outputting the updated value kT(i) hashed with key(i) (ie same key for
all sessions of identity i),
- and a system outputting a fresh name at each session.
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

(* Stef: Inutile cette induction *)

goal stateUpdate :
forall (t:timestamp), (forall (i,j:index), t=T(i,j) => kT(i)@t = hkey(kT(i)@pred(t),key(i))).
Proof.
simpl. 
(* induction. *) 
Qed.

goal onlyTagActions :
forall (t:timestamp), t <> init => exists (i,j:index), t=T(i,j).
Proof.
intro *.
case t.
Qed.

goal notInit :
forall (t:timestamp), (exists (t':timestamp), t' < t)  => (t <> init).
Proof.
intro *.
Qed.

(* kT(i)@t = kT(i)@t' where t' is init or the previous update of kT(i) *)
goal lastUpdate_ : forall (t:timestamp) forall (i:index)
  (kT(i)@t = kT(i)@init && forall (j':index) t < T(i,j')) ||
  (exists j:index,
   kT(i)@t = kT(i)@T(i,j) &&
   T(i,j) <= t &&
   (forall (j':index), T(i,j')<=T(i,j) || t<T(i,j'))).
Proof.
induction.
case t.
left.
case H.
assert (i=i1 || i<>i1).
case H0.

(* t = T(i,j) *)
right; exists j.

(* t = T(i1,j) with i<>i1 *)
assert kT(i)@t = kT(i)@pred(t).
use IH0 with pred(T(i1,j)).
use H0 with i.
case H1.

  left.
  use H1 with j'.

  right.
  exists j1.
  use H1 with j'.
(* Stef: je detaille plus pour comprendre ce qui se passe *)
nosimpl(case H2).
  simpl.
nosimpl(right).
simpl. (* Stef: sur celui-ci je ne vois  pas le raisonnement que fait squirrel*)
(* t = init *)
left.

Qed.

(* A more convenient version of the lemma, because our use
   tactic is too primitive. *)
goal lastUpdate : forall (t:timestamp,i:index)
  (kT(i)@t = kT(i)@init && forall (j':index) t < T(i,j')) ||
  (exists j:index,
   kT(i)@t = kT(i)@T(i,j) &&
   T(i,j) <= t &&
   (forall (j':index), T(i,j')<=T(i,j) || t<T(i,j'))).
Proof.
  intros.
  use lastUpdate_ with t.
  use H0 with i.
Qed.

goal stateInequality :
  forall (t:timestamp),
  (forall (t':timestamp), forall (i,j,i':index)
     t = T(i,j) && t' < t => kT(i)@t <> kT(i')@t').
Proof.
induction.
substitute t, T(i,j).
assert kT(i')@t' = hkey(kT(i)@pred(T(i,j)),key(i)).
euf M1.

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
use H1 with j1; case H0.

(* kT(i)@pred(T(i,j)) = kT(i)@T(i,j2)
   then we should have that T(i,j1) <= T(i,j2) *)
assert (T(i,j1) <= T(i,j2)).
use H1 with j1; case H2; case H0.

use IH0 with T(i,j2).
use H2 with pred(T(i,j1)).
use H3 with i,j2,i.

Qed.

(*
Ancienne preuve de Solene un peu compliquee
goal stateInequalityHelpful :
(forall (i,j,j':index), T(i,j')<T(i,j) => kT(i)@pred(T(i,j)) <> kT(i)@pred(T(i,j'))).
Proof.
intros.
use lastUpdate with pred(T(i,j)),i.
case H0.
(* Case init *)
use H0 with j'.
use stateInequality with T(i,j1).
use H1 with pred(T(i,j')).
use H2 with i,j1,i.
use H0 with j'. case H3.
Qed.
*)


goal stateInequalityHelpful :
(forall (i,j,j':index), T(i,j')<T(i,j) => kT(i)@pred(T(i,j)) <> kT(i)@pred(T(i,j'))).
Proof.
intros.
use stateInequality with T(i,j).
use H0 with T(i,j').
use H1 with i,j,i.
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
