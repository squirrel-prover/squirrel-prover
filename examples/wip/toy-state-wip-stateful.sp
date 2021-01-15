(*******************************************************************************
TOY EXAMPLE WITH STATE
*******************************************************************************)

hash h

abstract ok : message
abstract ko : message

name seed : index->message
name key : index->message
name n : index->index->message
name nIdeal : index->index->message

channel cT
channel cR

mutable kT : index->message
mutable kR : index->message

axiom stateTagInit :
  forall (i:index), kT(i)@init = seed(i)
axiom stateReaderInit :
  forall (ii:index), kR(ii)@init = seed(ii)

process tag(i:index,j:index) =
  kT(i) := h(diff(kT(i),nIdeal(i,j)),key(i));
  out(cT, kT(i))

process reader(k:index) =
  in(cT,x);
  try find ii,jj such that x = h(diff(kR(ii),nIdeal(ii,jj)),key(ii)) in
    kR(ii) := diff(h(kR(ii),key(ii)), h(nIdeal(ii,jj),key(ii)));
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

goal [left] matchingStates : 
forall (i,j,jj,k:index),
  exec@T(i,j) && R(k,i,jj) < T(i,j)
  => kT(i)@pred(T(i,j)) <> kR(i)@pred(R(k,i,jj)).
Proof.
intros.
executable T(i,j).
apply H1 to R(k,i,jj).
expand exec@R(k,i,jj). expand cond@R(k,i,jj).
euf M1.
admit.
assert kT(i)@pred(T(i,j)) = kT(i)@pred(T(i,j1)).
assert T(i,j1) < T(i,j).
admit.
Qed.

goal [left] stateInequalityTag :
forall (i,j,j':index)
  T(i,j) < T(i,j') => kT(i)@T(i,j) <> kT(i)@T(i,j').
Proof.
admit.
Qed.

goal [left] stateInequalityReader :
forall (k,k',ii,jj,jj':index)
  R(k,ii,jj) < R(k',ii,jj') => kR(ii)@R(k,ii,jj) <> kR(ii)@R(k',ii,jj').
Proof.
admit.
Qed.

goal [right] readerPlaysAfterTag :
forall (t:timestamp),
forall (ii,jj,k:index),
  t = R(k,ii,jj) && exec@T(ii,jj) && R(k,ii,jj) < T(ii,jj) => False.
Proof.
induction.
executable T(ii,jj).
apply H1 to R(k,ii,jj).
expand exec@R(k,ii,jj). expand cond@R(k,ii,jj).
euf M0.
apply IH0 to R(k1,ii,jj).
apply H3 to ii,jj,k1.
Qed.

equiv real_ideal.
Proof.
induction t.

expand frame@R(k,ii,jj).
fa 0.
fa 1.
expand output@R(k,ii,jj).
expand exec@R(k,ii,jj).
equivalent 
  cond@R(k,ii,jj),
  diff(
    exists (j:index), T(ii,j) < R(k,ii,jj) && output@T(ii,j) = input@R(k,ii,jj),
    T(ii,jj) < R(k,ii,jj) && output@T(ii,jj) = input@R(k,ii,jj)
  ).

split.

(* cond => honest *)
project.
(* LEFT *)
expand cond@R(k,ii,jj).
euf M0.
apply stateInequalityReader to k1,k,ii,jj1,jj.
exists j.
(* RIGHT *)
expand cond@R(k,ii,jj).
euf M0.
admit. (* need induction? *)

(* honest => cond *)
project.
(* LEFT *)
expand cond@R(k,ii,jj).
admit. (* ??? *)
(* RIGHT *)
expand cond@R(k,ii,jj).

admit. (* we should be able to use fadup 1. *)

admit.

expandall.
fa 0. fa 1.
prf 1.
ifcond 1,exec@pred(T(i,j)).
fa 1.
yesif 1.
project.
split.

apply matchingStates to i,j,jj,k.
expand exec@T(i,j).
expand cond@T(i,j).

apply stateInequalityTag to i,j1,j.

apply readerPlaysAfterTag to R(k,ii,jj). 
apply H1 to ii,jj,k.
expand exec@T(ii,jj).
expand cond@T(ii,jj).

fresh 1.
Qed.
