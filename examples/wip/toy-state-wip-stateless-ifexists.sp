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

process tag(i:index,j:index) =
  (*kT(i) := hkey(kT(i),key(i));*)
  out(cT, diff(h(n(i,j),key(i)),h(nIdeal(i,j),key(i))))

process reader(k:index) =
  in(cT,x);
  if exists (ii,jj:index), x = diff(h(n(ii,jj),key(ii)), h(nIdeal(ii,jj),key(ii))) then
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

goal wa_R :
forall (k:index),
  cond@R(k) <=>
  exists (i,j:index), T(i,j) < R(k) && output@T(i,j) = input@R(k).
Proof.
intros.
split.
expand cond@R(k).

project.
euf M0.
exists ii,j.
euf M0.
exists ii,j.

expand cond@R(k).
exists i,j.
Qed.

goal wa_R1 :
forall (k:index),
  cond@R1(k) <=>
  not(exists (i,j:index), T(i,j) < R1(k) && output@T(i,j) = input@R1(k)).
Proof.
intros.
split.
expand cond@R1(k).

notleft H0.
apply H0 to i,j.

expand cond@R1(k).
project.
euf M0.
notleft H0.
apply H0 to ii,j.
case H1.
euf M0.
notleft H0.
apply H0 to ii,j.
case H1.
Qed.

equiv real_ideal.
Proof.
induction t.

expand frame@R(k).
fa 0.
fa 1.
expand output@R(k).
expand exec@R(k).
equivalent
  cond@R(k),
  exists (i,j:index), T(i,j) < R(k) && output@T(i,j) = input@R(k).
apply wa_R to k.
fadup 1.

expand frame@R1(k).
fa 0.
fa 1.
expand output@R1(k).
expand exec@R1(k).
equivalent
  cond@R1(k),
  not (exists (i,j:index), T(i,j) < R1(k) && output@T(i,j) = input@R1(k)).
apply wa_R1 to k.
fadup 1.

expandall.
fa 0. fa 1. fa 1.
prf 1.
yesif 1.
project.
fresh 1.
Qed.
