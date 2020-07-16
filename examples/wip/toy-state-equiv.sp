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
induction.
Qed.

goal stateInequality :
forall (t:timestamp),
  (forall (t':timestamp), forall (i,j,j':index), t=T(i,j) && t'=T(i,j') && t'<t => kT(i)@t <> kT(i)@t').
Proof.
induction.
assert hkey(kT(i)@pred(T(i,j')),key(i)) = hkey(kT(i)@pred(T(i,j)),key(i)).
euf M3.
apply IH0 to t'.
(* ne fonctionne pas comme attendu :
toutes les occurences de t1 ne sont pas remplacées par t'
semble venir de filter_subst qui ignore les variables sur lesquelles sont quantifiés les forall *)
admit. admit.
Qed.

goal stateInequalityHelpful :
(forall (i,j,i',j':index), T(i',j')<T(i,j) => kT(i)@pred(T(i,j)) <> kT(i)@pred(T(i',j'))).
Proof.
intros.
assert pred(T(i',j')) < pred(T(i,j)).
apply stateInequality to pred(T(i,j)). 
(* ne fonctionne pas comme attendu :
semble venir du fait que pred(T(i,j)) n'est pas une variable donc la substitution ne s'applique pas *)
admit.
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
apply stateInequalityHelpful to i,j,i,j1.
fresh 1. yesif 1.
Qed.
