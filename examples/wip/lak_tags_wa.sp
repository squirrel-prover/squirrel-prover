(* R --> T: nr                                    *)
(* T --> R: nT, h(<nR, nT, tag1>, k)              *)
(* R --> T: h(<h(<nR, nT, tag2>, k), nr, tag2>,k) *)

hash h

abstract ok:message
abstract ko:message

abstract tag1:message
abstract tag2:message
axiom tags_neq : tag1 <> tag2

name key : index->message

channel cT
channel cR

process tag(i:index,k:index) =
  new nT;
  in(cR,nR);
  out(cT,<nT,h(<<nR,nT>,tag1>,key(i))>);
  in(cR,m3);
  if m3 = h(<<h(<<nR,nT>,tag1>,key(i)),nR>,tag2>,key(i)) then
    out(cT,ok)
  else
    out(cT,ko)

process reader(j:index) =
  new nR;
  out(cR,nR);
  in(cT,x);
  try find i such that snd(x) = h(<<nR,fst(x)>,tag1>,key(i)) in
    out(cR,h(<<snd(x),nR>,tag2>,key(i)))
  else
    out(cR,ko)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).


goal wa_R:
  forall (j:index, i:index),
  cond@R1(j,i) =>
  exists (k:index),
  T(i,k) < R1(j,i) &&
  fst(input@R1(j,i)) = fst(output@T(i,k)) &&
  snd(input@R1(j,i)) = snd(output@T(i,k)) && R(j) < T(i,k) && output@R(j) = input@T(i,k).
Proof.
simpl.
expand cond@R1(j,i).
euf M0.
use tags_neq.
exists k.
assert (nR(j) = input@T(i,k)).
fresh M2.
depends R(j), R2(j).
depends R(j), R1(j,i1).
Qed.


goal wa_T:
 forall (i:index, k:index),
 exec@T1(i,k) =>
 exists (j:index),
 R1(j,i) < T1(i,k) &&
 output@R1(j,i) = input@T1(i,k) &&
 T(i,k) < R1(j,i) &&
 fst(output@T(i,k)) = fst(input@R1(j,i)) &&  snd(output@T(i,k)) = snd(input@R1(j,i)) &&
 R(j) < T(i,k) &&
 output@R(j) = input@T(i,k).
Proof.
intros.
assert cond@T1(i,k).
expand exec@T1(i,k).
expand cond@T1(i,k).
use tags_neq.
euf M0.
assert (snd(input@R1(j,i)) = h(<<input@T(i,k),nT(i,k)>,tag1>,key(i))).
euf M3.
case H2.
case H1.

nosimpl(exists j).
nosimpl(assert cond@R1(j,i)).
executable T1(i,k).
use H1 with R1(j,i).
expand exec@R1(j,i).
nosimpl(expand cond@R1(j,i)).

repeat split.

collision. (* M3 and M4 together give a collision that allows to conclude. *)

assert (input@T(i,k) = nR(j)). 
fresh M5.
depends R(j), R2(j).
depends R(j), R1(j,i1).
Qed.
