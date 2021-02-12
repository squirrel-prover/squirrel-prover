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

mutable kT : index->message

channel cT

process tag(i:index,j:index) =
  kT(i) := hkey(kT(i),key(i));
  out(cT, diff(kT(i),n(i,j)))

system (!_i !_j T: tag(i,j)).

(* GOALS *)

goal stateUpdate :
forall (t:timestamp), (forall (i,j:index), 
  t=T(i,j) => kT(i)@t = hkey(kT(i)@pred(t),key(i))).
Proof.
simpl.
Qed.

goal onlyTagActions :
forall (t:timestamp), t <> init => exists (i,j:index), t=T(i,j).
Proof.
intro t Hneq.
case t. 
Qed.

goal notInit :
forall (t:timestamp), (exists (t':timestamp), t' < t)  => (t <> init).
Proof.
auto. 
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

(* t = init *)
by left.

(* t = T(i1,j) *)
assert (i=i1 || i<>i1).
case H0.

(* t = T(i,j) *)
by right; exists j.

(* t = T(i1,j) with i<>i1 *)
substitute t,T(i1,j).
assert kT(i)@T(i1,j) = kT(i)@pred(T(i1,j)).
expand kT(i)@T(i1,j).
by noif.
apply H to pred(T(i1,j)).
apply H0 to i.
case H1.

  left.
  by apply H1 to j'.

  right.
  exists j1.
  apply H2 to j'.
  by case H1.
Qed.

(* A more convenient version of the lemma, because our apply
   tactic is too primitive. *)
goal lastUpdate : forall (t:timestamp,i:index)
  (kT(i)@t = kT(i)@init && forall (j':index) t < T(i,j')) ||
  (exists j:index,
   kT(i)@t = kT(i)@T(i,j) &&
   T(i,j) <= t &&
   (forall (j':index), T(i,j')<=T(i,j) || t<T(i,j'))).
Proof.
  intro t i.
  apply lastUpdate_ to t.
  apply H to i.
Qed.

goal stateInequality :
  forall (t:timestamp),
  (forall (t':timestamp), forall (i,j,i':index)
     t = T(i,j) && t' < t => kT(i)@t <> kT(i')@t').
Proof.
induction.
substitute t, T(i,j).
assert kT(i')@t' = hkey(kT(i)@pred(T(i,j)),key(i)).
euf Meq0.

(* T(i,j1) < T(i,j)
   kT(i)@pred(T(i,j1)) = kT(i)@pred(T(i,j))
   in order to apply IH0 we need timestamps of the form T(i,_)
   but pred(_) has no reason to be of that form...
   this is where lastUpdate comes into play *)

apply lastUpdate to pred(T(i,j)),i.
case H1.

(* kT(i)@pred(T(i,j)) = kT(i)@init
   this can actually happen only if tag i has not played from init to pred(T(i,j))
   but we know that T(i,j1) < T(i,j): absurd *)
by apply H1 to j1; case H0.

(* kT(i)@pred(T(i,j)) = kT(i)@T(i,j2)
   then we should have that T(i,j1) <= T(i,j2) *)
assert (T(i,j1) <= T(i,j2)).
by apply H2 to j1; case H1; case H0.

apply H to T(i,j2).
apply H1 to pred(T(i,j1)).
apply H3 to i,j2,i.

Qed.

goal stateInequalityHelpful :
(forall (i,j,j':index), T(i,j')<T(i,j) => kT(i)@pred(T(i,j)) <> kT(i)@pred(T(i,j'))).
Proof.
intro i j j' Hlt Heq.
apply stateInequality to T(i,j).
apply H to T(i,j').
apply H0 to i,j,i.
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
apply stateInequalityHelpful to i,j,j1.
fresh 1. yesif 1.
Qed.
