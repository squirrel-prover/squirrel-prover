hash h

abstract ok:message
abstract ko:message

abstract tag1:message
abstract tag2:message
axiom tags_neq : tag1 <> tag2

name key : index->message
name key': index->index->message
channel cT
channel cR

process tag(i:index,k:index) =
  new nT;
  in(cR,nR);
  let m2 = h(<<nR,nT>,tag1>,diff(key(i),key'(i,k))) in
  out(cT,<nT,m2>);
  in(cR,m3);
  if m3 = h(<<m2,nR>,tag2>,diff(key(i),key'(i,k))) then
    out(cT,ok)
  else
    out(cT,ko)

process reader(j:index) =
  new nR;
  out(cR,nR);
  in(cT,x);
  try find i,k such that snd(x) = h(<<nR,fst(x)>,tag1>,diff(key(i),key'(i,k))) in
    out(cR,h(<<snd(x),nR>,tag2>,diff(key(i),key'(i,k))))
  else
    out(cR,ko)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).



goal [left] wa_left :
  forall (i:index, j:index, k:index),
  cond@R1(j,i,k) =>
  exists (ii:index,kk:index),
  T(ii,kk) <= R1(j,i,k) &&
  fst(input@R1(j,i,k)) = fst(output@T(ii,kk)) &&
  snd(input@R1(j,i,k)) = snd(output@T(ii,kk)).
Proof.
simpl.
expand cond@R1(j,i,k).
use tags_neq.
euf M0.
exists i,k1.
Qed.

goal [right] wa_right:
  forall (i:index, j:index, k:index),
  cond@R1(j,i,k) =>
  exists (ii:index,kk:index),
  T(ii,kk) <= R1(j,i,k) &&
  fst(input@R1(j,i,k)) = fst(output@T(ii,kk)) &&
  snd(input@R1(j,i,k)) = snd(output@T(ii,kk)).
Proof.
simpl.
expand cond@R1(j,i,k).
use tags_neq.
euf M0.
exists i,k.
Qed.


equiv foo.
Proof.
induction t.
(* Case R: OK *)
expand frame@R(j); expand exec@R(j).
expand cond@R(j); expand output@R(j).
fa 1; fa 2.
fresh 2; yesif 2.
repeat split.
depends R(j1), R1(j1,i,k).
depends R(j1), R2(j1).

(* Case R1 *)
expand frame@R1(j,i,k); expand exec@R1(j,i,k).
expand cond@R1(j,i,k); expand output@R1(j,i,k).
fa 0.
fa 2.
fa 3.
prf 3.
yesif 3.
intro.
(* QUE FAIRE ICI ?*)
help.
intro.

(* Case R2 *)
admit.


(* Case T *)
admit.

(* Case T1 *)
admit.
(* Case T2 *)
admit.
Qed.




