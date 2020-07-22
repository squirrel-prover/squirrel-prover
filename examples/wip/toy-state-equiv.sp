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

goal stateInequality :
forall (t:timestamp),
  (forall (t':timestamp), forall (i,j,i',j':index), 
    t=T(i,j) && t'=T(i',j') && t'<t => kT(i)@t <> kT(i')@t').
Proof.
induction.
assert hkey(kT(i')@pred(T(i',j')),key(i')) = hkey(kT(i)@pred(T(i,j)),key(i)).
euf M3.

(* case euf n°1 - exists T(i',j1), kT(i')@pred(T(i',j1)) = kT(i')@pred(T(i',j')) *)
assert (pred(T(i',j1)) < pred(T(i',j')) || (pred(T(i',j1)) < pred(T(i,j)) && pred(T(i',j1)) > pred(T(i',j')))).
case H0. left. right. admit.
case H1.
(* case H1 - pred(T(i',j1)) < pred(T(i',j')) *)
assert pred(T(i',j1)) < pred(T(i',j')).
apply IH0 to pred(T(i',j')).
apply H1 to pred(T(i',j1)).
apply onlyTagActions to pred(T(i',j')).
apply onlyTagActions to pred(T(i',j1)).
apply H2 to i1,j2,i2,j3.
assert (i'=i1 || i'<>i1). case H3. assert (i'=i2 || i'<>i2). case H3.
admit. (* case i' = i1 && i' <> i2 *) 
admit. (* case i' <> i1 && i' = i2 *) 
admit. (* TODO BASE CASE *)
apply notInit to pred(T(i',j')). exists pred(T(i',j1)).
(* case H1 - pred(T(i',j1)) < pred(T(i,j)) && pred(T(i',j1)) > pred(T(i',j')) *)
apply IH0 to pred(T(i',j1)).
apply H1 to pred(T(i',j')).
apply onlyTagActions to pred(T(i',j1)).
apply onlyTagActions to pred(T(i',j')).
apply H2 to i1,j2,i2,j3.
assert (i'=i1 || i'<>i1). case H3. assert (i'=i2 || i'<>i2). case H3.
admit. (* case i' = i1 && i' <> i2 *) 
admit. (* case i' <> i1 && i' = i2 *) 
admit. (* TODO BASE CASE *)
apply notInit to pred(T(i',j1)). exists pred(T(i',j')).

(* case euf n°2 - i=i' and kT(i')@pred(T(i',j)) = kT(i')@pred(T(i',j')) *)
assert pred(T(i',j)) > T(i',j') || pred(T(i',j)) < T(i',j') || pred(T(i',j)) = T(i',j').
case H0.
(* case H0 - pred(T(i',j)) > T(i',j') *)
apply IH0 to pred(T(i',j)).
apply H0 to pred(T(i',j')).
apply onlyTagActions to pred(T(i',j)).
apply onlyTagActions to pred(T(i',j')).
apply H1 to i,j1,i1,j2.
assert (i'=i1 || i'<>i1). case H2. assert (i'=i || i'<>i). case H2.
admit. (* case i' = i1 && i' <> i *)
assert (i'=i || i'<>i). case H2.
admit. (* case i' <> i1 && i' = i *) 
admit. (* case i' <> i1 && i' <> i *) 
admit. (* TODO BASE CASE *)
apply notInit to pred(T(i',j)). exists T(i',j').
(* case H0 - pred(T(i',j)) = T(i',j') *)
apply IH0 to pred(T(i',j)).
apply H0 to pred(T(i',j')).
apply onlyTagActions to pred(T(i',j)).
apply onlyTagActions to pred(T(i',j')).
apply H1 to i,j1,i1,j2.
assert (i'=i1 || i'<>i1). case H2. assert (i'=i || i'<>i). case H2.
assert (i'=i || i'<>i). case H2.
admit. (* case i' <> i1 && i' = i *) 
admit. (* TODO BASE CASE *)
Qed.

goal stateInequalityHelpful :
(forall (i,j,i',j':index), T(i',j')<T(i,j) => kT(i)@pred(T(i,j)) <> kT(i')@pred(T(i',j'))).
Proof.
intros.
assert pred(T(i',j')) < pred(T(i,j)).
apply stateInequality to pred(T(i,j)). 
apply H0 to pred(T(i',j')).
apply onlyTagActions to pred(T(i,j)).
apply onlyTagActions to pred(T(i',j')).
apply H1 to i1,j1,i2,j2.
admit. (* TODO *)
admit. (* TODO BASE CASE *)
apply notInit to pred(T(i,j)). exists pred(T(i',j')).
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
