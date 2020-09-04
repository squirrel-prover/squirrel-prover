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

mutable kT : index->message

channel cT

axiom stateInit :
  forall (i:index), kT(i)@init = seed(i)

process tag(i:index,j:index) =
  kT(i) := hkey(kT(i),key(i));
  out(cT, diff(kT(i),n(i,j)))

system (!_i !_j T: tag(i,j)).

goal stateUpdate :
forall (t:timestamp), (forall (i,j:index), t=T(i,j) => kT(i)@t = hkey(kT(i)@pred(t),key(i))).
Proof.
simpl.
Qed.

goal onlyTagActions :
forall (t:timestamp), t <> init => exists (i,j:index), t=T(i,j).
Proof.
intros.
case t. case H0.
Qed.

goal notInit :
forall (t:timestamp), (exists (t':timestamp), t' < t)  => (t <> init).
Proof.
intros.
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
case H0.
assert (i=i1 || i<>i1).
case H0.

(* t = T(i,j) *)
right. exists j.

(* t = T(i1,j) with i<>i1 *)
substitute t,T(i1,j).
assert kT(i)@T(i1,j) = kT(i)@pred(T(i1,j)).
expand kT(i)@T(i1,j).
noif.
apply IH0 to pred(T(i1,j)).
apply H0 to i.
case H1.

  left.
  apply H1 to j'.

  right.
  exists j1.
  apply H1 to j'.
  case H2.

(* t = init *)
left.
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
  intros.
  apply lastUpdate_ to t.
  apply H0 to i.
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
   in order to apply IH0 we need timestamps of the form T(i,_)
   but pred(_) has no reason to be of that form...
   this is where lastUpdate comes into play *)

apply lastUpdate to pred(T(i,j)),i.
case H1.

(* kT(i)@pred(T(i,j)) = kT(i)@init
   this can actually happen only if tag i has not played from init to pred(T(i,j))
   but we know that T(i,j1) < T(i,j): absurd *)
apply H1 to j1; case H0.

(* kT(i)@pred(T(i,j)) = kT(i)@T(i,j2)
   then we should have that T(i,j1) <= T(i,j2) *)
assert (T(i,j1) <= T(i,j2)).
apply H1 to j1; case H2; case H0.

apply IH0 to T(i,j2).
apply H2 to pred(T(i,j1)).
apply H3 to i,j2,i.

Qed.

goal stateInequalityHelpful :
(forall (i,j,j':index), T(i,j')<T(i,j) => kT(i)@pred(T(i,j)) <> kT(i)@pred(T(i,j'))).
Proof.
intros.
apply stateInequality to T(i,j).
apply H0 to T(i,j').
apply H1 to i,j,i.
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
