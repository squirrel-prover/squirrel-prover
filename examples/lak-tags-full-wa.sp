(* Full model of LAK with pairs and tags, for authentication only. *)

(* R --> T: nr                                    *)
(* T --> R: nT, h(<nR, nT, tag1>, k)              *)
(* R --> T: h(<h(<nR, nT, tag2>, k), nr, tag2>,k) *)

set timeout=4. 

hash h

abstract ok:message
abstract ko:message

abstract tag1:message
abstract tag2:message

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

axiom tags_neq : tag1 <> tag2.

goal wa_R:
  forall (j:index, i:index),
  happens(R1(j,i)) =>
  cond@R1(j,i) =>
  exists (k:index),
  T(i,k) < R1(j,i) &&
  fst(input@R1(j,i)) = fst(output@T(i,k)) &&
  snd(input@R1(j,i)) = snd(output@T(i,k)) && R(j) < T(i,k) && output@R(j) = input@T(i,k).
Proof.
simpl.
expand cond@R1(j,i).
euf H.
use tags_neq.
exists k.
assert (nR(j) = input@T(i,k)).
fresh Meq0.
case H0.
depends R(j), R2(j).
depends R(j), R1(j,i0).
Qed.

goal executable_R1 (t:timestamp) (j,i:index) :
  happens(t) => exec@t => R1(j,i)<=t => exec@R1(j,i) && cond@R1(j,i).
Proof.
  intro *.
  executable t.
  use H0 with R1(j,i).
  expand exec@R1(j,i).
Qed.

goal wa_T:
 forall (i:index, k:index),
 happens(T1(i,k)) => exec@T1(i,k) =>
 exists (j:index),
 R1(j,i) < T1(i,k) &&
 output@R1(j,i) = input@T1(i,k) &&
 T(i,k) < R1(j,i) &&
 fst(output@T(i,k)) = fst(input@R1(j,i)) &&  snd(output@T(i,k)) = snd(input@R1(j,i)) &&
 R(j) < T(i,k) &&
 output@R(j) = input@T(i,k).
Proof.
  intro *.
  assert cond@T1(i,k).
  expand exec@T1(i,k).
  expand cond@T1(i,k).
  use tags_neq.
  euf H0.
  assert (snd(input@R1(j,i)) = h(<<input@T(i,k),nT(i,k)>,tag1>,key(i))).
  euf Meq0.
  case H2.
  case H1.
  nosimpl(exists j).
  use executable_R1 with T1(i,k),j,i.
  expand cond@R1(j,i).
  assert h(<<nR(j),fst(input@R1(j,i))>,tag1>,key(i)) =
         h(<<input@T(i,k),nT(i,k)>,tag1>,key(i)) as Hcoll;
    [0: congruence].
  collision Hcoll.
  assert (input@T(i,k) = nR(j)) as Hfresh;
    [0: congruence].
  fresh Hfresh.
  case H5.
  by depends R(j), R2(j).
  by depends R(j), R1(j,i0).
Qed.
