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
  if exists (i,k:index),
     snd(x) = h(<<nR,fst(x)>,tag1>,diff(key(i),key'(i,k)))
  then
    out(cR, try find i,k such that
              snd(x) = h(<<nR,fst(x)>,tag1>,diff(key(i),key'(i,k)))
            in
              h(<<snd(x),nR>,tag2>,diff(key(i),key'(i,k))))
  else
    out(cR,ko)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

goal wa_R1: forall j:index,
  (exists (i,k:index),
   snd(input@R1(j)) =
   h(<<nR(j),fst(input@R1(j))>,tag1>,diff(key(i),key'(i,k))))
  <=>
  (exists (i,k:index),
   T(i,k) < R1(j) &&
   snd(output@T(i,k)) = snd(input@R1(j)) &&
   fst(output@T(i,k)) = fst(input@R1(j)) &&
   R(j) < T(i,k) && input@T(i,k) = output@R(j)).

Proof.
intros; split.
(* cond => wa *)
use tags_neq; project.
(* LEFT *)
euf M0.
exists i,k1.
assert input@T(i,k1)=nR(j).
fresh M3.
depends R(j),R2(j).
(* RIGHT *)
euf M0.
exists i,k.
assert input@T(i,k)=nR(j).
fresh M3.
depends R(j),R2(j).
(* wa => cond *)
exists i,k.
Qed.

goal wa_R2: forall j:index,
  (exists (i,k:index),
   snd(input@R2(j)) =
   h(<<nR(j),fst(input@R2(j))>,tag1>,diff(key(i),key'(i,k))))
  <=>
  (exists (i,k:index),
   T(i,k) < R2(j) &&
   snd(output@T(i,k)) = snd(input@R2(j)) &&
   fst(output@T(i,k)) = fst(input@R2(j)) &&
   R(j) < T(i,k) && input@T(i,k) = output@R(j)).

Proof.
intros; split.
(* cond => wa *)
use tags_neq; project.
(* LEFT *)
euf M0.
exists i,k1.
assert input@T(i,k1)=nR(j).
fresh M3.
depends R(j),R1(j).
(* RIGHT *)
euf M0.
exists i,k.
assert input@T(i,k)=nR(j).
fresh M3.
depends R(j),R1(j).
(* wa => cond *)
exists i,k.
Qed.

goal [left] wa_R1_left: forall (i,j:index),
  snd(input@R1(j)) =
  h(<<nR(j),fst(input@R1(j))>,tag1>,key(i))
  <=>
  exists k:index,
  T(i,k) < R1(j) &&
  snd(output@T(i,k)) = snd(input@R1(j)) &&
  fst(output@T(i,k)) = fst(input@R1(j)) &&
  R(j) < T(i,k) && input@T(i,k) = output@R(j).

Proof.
intros.
use tags_neq.
euf M0.
exists k.
assert input@T(i,k)=nR(j).
fresh M3.
depends R(j),R2(j).
Qed.

goal [right] wa_R1_right: forall (i,j,k:index),
  snd(input@R1(j)) =
  h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k))
  <=>
  T(i,k) < R1(j) &&
  snd(output@T(i,k)) = snd(input@R1(j)) &&
  fst(output@T(i,k)) = fst(input@R1(j)) &&
  R(j) < T(i,k) && input@T(i,k) = output@R(j).

Proof.
intros.
use tags_neq.
euf M0.
assert input@T(i,k)=nR(j).
fresh M3.
depends R(j),R2(j).
Qed.


equiv unlinkability.
Proof.
induction t.


(* Case R: OK *)
expand frame@R(j); expand exec@R(j).
expand cond@R(j); expand output@R(j).
fa 1; fa 2.
fresh 2; yesif 2.
repeat split.
depends R(j),R2(j).
depends R(j),R1(j).

(* Case R1: OK *)
expand frame@R1(j); expand exec@R1(j).
expand cond@R1(j); expand output@R1(j).

equivalent
  (exists (i,k:index),
   snd(input@R1(j)) =
   h(<<nR(j),fst(input@R1(j))>,tag1>,diff(key(i),key'(i,k)))),
  (exists (i,k:index),
   T(i,k) < R1(j) &&
   snd(output@T(i,k)) = snd(input@R1(j)) &&
   fst(output@T(i,k)) = fst(input@R1(j)) &&
   R(j) < T(i,k) && input@T(i,k) = output@R(j)).

use wa_R1 with j.

equivalent
  (if exec@pred(R1(j)) &&
      exists (i,k:index),
      (((T(i,k) < R1(j) && snd(output@T(i,k)) = snd(input@R1(j))) &&
      fst(output@T(i,k)) = fst(input@R1(j))) &&
      R(j) < T(i,k) && input@T(i,k) = output@R(j))
   then (try find i,k such that
           snd(input@R1(j)) =
           h(<<nR(j),fst(input@R1(j))>,tag1>,diff(key(i),key'(i,k)))
         in
           h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k))))),
  (if exec@pred(R1(j)) &&
      exists (i,k:index),
      (T(i,k) < R1(j) && snd(output@T(i,k)) = snd(input@R1(j)) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      R(j) < T(i,k) && input@T(i,k) = output@R(j))
   then (try find i,k such that
          (exec@pred(R1(j)) &&
	   (T(i,k) < R1(j) && snd(output@T(i,k)) = snd(input@R1(j)) &&
	    fst(output@T(i,k)) = fst(input@R1(j)) &&
	    R(j) < T(i,k) && input@T(i,k) = output@R(j)))
         in
	   if exec@pred(R1(j))
	   then h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k))))).
fa.
exists i,k.
exists i,k.
project.
(* LEFT *)
fa.
use wa_R1_left with i1,j.
use H1.
exists k.
yesif.
(* RIGHT *)
fa.
use wa_R1_right with i1,j,k1.
use H1.
yesif.

fa 1. fadup 0.
fa 2. fadup 2.
fa 2. fadup 2.
prf 2.
ifcond 2, exec@pred(R1(j)).
fa 2.
yesif 2.
use tags_neq; project.
fresh 2.

(* Case R2: OK *)
expand frame@R2(j); expand exec@R2(j).
expand cond@R2(j); expand output@R2(j).

equivalent
  (exists (i,k:index),
   snd(input@R2(j)) =
   h(<<nR(j),fst(input@R2(j))>,tag1>,diff(key(i),key'(i,k)))),
  (exists (i,k:index),
   T(i,k) < R2(j) &&
   snd(output@T(i,k)) = snd(input@R2(j)) &&
   fst(output@T(i,k)) = fst(input@R2(j)) &&
   R(j) < T(i,k) && input@T(i,k) = output@R(j)).

use wa_R2 with j.

fadup 0.

(* Case T: OK *)
expand frame@T(i,k); expand exec@T(i,k).
expand cond@T(i,k);expand output@T(i,k).
expand m2(i,k)@T(i,k).
fa 1.
fa 2.
fa 2.
prf 3.
yesif 3.
use tags_neq; project.
assert fst(input@R1(j))=nT(i,k).
fresh M2.
depends T(i,k),T2(i,k).
depends T(i,k),T1(i,k).
assert fst(input@R1(j))=nT(i,k).
fresh M2.
depends T(i,k),T2(i,k).
depends T(i,k),T1(i,k).
fresh 3.
fresh 2.
yesif 2.
repeat split.
depends T(i,k),T1(i,k).
depends T(i,k),T2(i,k).

(* Case T1: TODO *)
admit.

(* Case T2: TODO *)
admit.
Qed.
