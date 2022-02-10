(* This is a full model of LAK with pairs and tags, ie. it includes the last conditional
 * and message of tags. It contains admits and is broken due to the changes in the prover. *)

hash h

abstract ok:message
abstract ko:message

abstract tag1:message
abstract tag2:message

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

axiom tags_neq : tag1 <> tag2.

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
intro *; split.
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

enrich seq(j -> nR(j)).
enrich seq(i,k -> nT(i,k)).
enrich seq(i,k -> h(<<input@T(i,k),nT(i,k)>,tag1>,diff(key(i),key'(i,k)))).
enrich seq(i,j,k -> h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k)))).

induction t.

admit. (* TODO lak-prelim *)

(* Case R: OK *)
expandseq seq(j->nR(j)), j.

(* Case R1: OK *)
expand frame, exec.
expand cond; expand output.

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

fa 5. fadup 4.
fa 6. fadup 6.
fa 6. fadup 6.
expandseq seq(i,j,k->h(<<snd(input@R1(j)),nR(j)>,tag2>,
                         diff(key(i),key'(i,k)))), i,j,k.

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

fadup 4.

(* Case T: OK *)
expandseq seq(i,k->nT(i,k)),i,k.
expandseq seq(i,k->h(<<input@T(i,k),nT(i,k)>,tag1>,diff(key(i),key'(i,k)))),i,k.

(* Case T1: OK *)
expand frame@T1(i,k); expand exec@T1(i,k).
equivalent exec@pred(T1(i,k)) && cond@T1(i,k),
  exec@pred(T1(i,k)) &&
  exists j:index,
  R1(j) < T1(i,k) &&
  input@T1(i,k) = output@R1(j) &&
  T(i,k) < R1(j) &&
  fst(input@R1(j)) = fst(output@T(i,k)) &&
  snd(input@R1(j)) = snd(output@T(i,k)) &&
  R(j) < T(i,k) &&
  input@T(i,k) = output@R(j).

expand cond@T1(i,k); split.

(* cond => honest *)
expand m2(i,k)@T1(i,k).
use tags_neq; project.
(* LEFT *)
euf M0.
assert R1(j) < T1(i,k).
  case H1.
  depends T(i,k),T1(i,k).
assert cond@R1(j).
  executable pred(T1(i,k)).
  use H2 with R1(j).
  expand exec@R1(j).
assert snd(input@R1(j)) = h(<<input@T(i,k),nT(i,k)>,tag1>,key(i)).
assert nR(j) = input@T(i,k).
euf M3. case H3.
assert R(j)<T(i,k).
  fresh M4. depends R(j),R2(j).
(** We now have R(j) < T(i,k) < R1(j) < T1(i,k). *)
(** Expanding cond@R1(j) does not bring much information:
    The condition of R1(j) holds for i,k but euf M0 does not provide this information.
    However the condition may also hold for other values i1,k1: nR(j) could have
    been sent to any tag, and any resulting output would work. *)

assert output@R1(j) = try find i,k such that
        snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key(i))
      in h(<<snd(input@R1(j)),nR(j)>,tag2>,key(i)).
case try find i,k such that
        snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key(i))
      in h(<<snd(input@R1(j)),nR(j)>,tag2>,key(i)).

(* If try-find is successful with i1,k1 we must have i1 = i (???)
   We know D0: output@R1(j) = h(<snd(input@R1(j)),nR(j)>,key(i1))
   but the hashed message can only depend *)
(* TODO euf D0 crashes here... I'm re-using wa_R1_left instead *)
use wa_R1_left with i1,j. use H3.
(* TODO understand why these "harmless" substitutions break the proof
subst fst(output@T(i1,k2)),nT(i1,k2).
subst fst(input@R1(j)),nT(i1,k2). *)
assert h(<<input@T(i,k),nT(i,k)>,tag1>,key(i)) = h(<<nR(j),nT(i1,k2)>,tag1>,key(i1)).
euf M10. (* This is almost a collision-resistance step *)

exists j.

(* If try-find fails, we contradict cond@R1(j).
   Here we do not care that this condition gives us uselessly new indices. *)
expand cond@R1(j).
use H2 with i1,k1.

(* RIGHT *)
euf M0.
assert R1(j) < T1(i,k).
  case H1.
  depends T(i,k),T1(i,k).
assert cond@R1(j).
  executable pred(T1(i,k)).
  use H2 with R1(j).
  expand exec@R1(j).
assert snd(input@R1(j)) = h(<<input@T(i,k),nT(i,k)>,tag1>,key'(i,k)).
assert nR(j) = input@T(i,k).
euf M3. case H3.
assert R(j)<T(i,k).
  fresh M4. depends R(j),R2(j).
assert output@R1(j) = try find i,k such that
        snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k))
      in h(<<snd(input@R1(j)),nR(j)>,tag2>,key'(i,k)).
case try find i,k such that
        snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k))
      in h(<<snd(input@R1(j)),nR(j)>,tag2>,key'(i,k)).

use wa_R1_right with i1,j,k1. use H3.
assert h(<<input@T(i,k),nT(i,k)>,tag1>,key'(i,k)) = h(<<nR(j),nT(i1,k1)>,tag1>,key'(i1,k1)).
euf M10. 
exists j.

expand cond@R1(j).
use H2 with i1,k1.

(* honest => cond *)
case output@R1(j).
expand m2(i,k)@T1(i,k).
project; euf M4.
false_left. false_left.
use H1 with i,k.

fa 5. fa 6. 
fadup 4.

(* Case T2: OK *)
expand frame@T2(i,k); expand exec@T2(i,k).
equivalent exec@pred(T2(i,k)) && cond@T2(i,k),
  exec@pred(T2(i,k)) &&
  not(exists j:index,
  R1(j) < T2(i,k) &&
  input@T2(i,k) = output@R1(j) &&
  T(i,k) < R1(j) &&
  fst(input@R1(j)) = fst(output@T(i,k)) &&
  snd(input@R1(j)) = snd(output@T(i,k)) &&
  R(j) < T(i,k) &&
  input@T(i,k) = output@R(j)).

expand cond@T2(i,k). split.
use H1.

(* honest => cond *)
case output@R1(j).
expand m2(i,k)@T2(i,k).
project; euf M4.
false_left. false_left.
use H2 with i,k.

(* cond => honest *)
expand m2(i,k)@T2(i,k).
use tags_neq; project.
(* LEFT *)
use H1.
euf M0.
assert R1(j) < T2(i,k).
  case H2.
  depends T(i,k),T2(i,k).
assert cond@R1(j).
  executable pred(T2(i,k)).
  use H3 with R1(j).
  expand exec@R1(j).
assert snd(input@R1(j)) = h(<<input@T(i,k),nT(i,k)>,tag1>,key(i)).
assert nR(j) = input@T(i,k).
euf M3. case H4.
assert R(j)<T(i,k).
  fresh M4. depends R(j),R2(j).
assert output@R1(j) = try find i,k such that
        snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key(i))
      in h(<<snd(input@R1(j)),nR(j)>,tag2>,key(i)).
case try find i,k such that
        snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key(i))
      in h(<<snd(input@R1(j)),nR(j)>,tag2>,key(i)).

use wa_R1_left with i1,j. use H4.
assert h(<<input@T(i,k),nT(i,k)>,tag1>,key(i)) = h(<<nR(j),nT(i1,k2)>,tag1>,key(i1)).
euf M10. 
exists j.

expand cond@R1(j).
use H3 with i1,k1.
(* RIGHT *)
euf M0.
assert R1(j) < T2(i,k).
  case H2.
  depends T(i,k),T2(i,k).
assert cond@R1(j).
  executable pred(T2(i,k)).
  use H3 with R1(j).
  expand exec@R1(j).
assert snd(input@R1(j)) = h(<<input@T(i,k),nT(i,k)>,tag1>,key'(i,k)).
assert nR(j) = input@T(i,k).
euf M3. case H4.
assert R(j)<T(i,k).
  fresh M4. depends R(j),R2(j).
assert output@R1(j) = try find i,k such that
        snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k))
      in h(<<snd(input@R1(j)),nR(j)>,tag2>,key'(i,k)).
case try find i,k such that
        snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k))
      in h(<<snd(input@R1(j)),nR(j)>,tag2>,key'(i,k)).

use wa_R1_right with i1,j,k1. use H4.
assert h(<<input@T(i,k),nT(i,k)>,tag1>,key'(i,k)) = h(<<nR(j),nT(i1,k1)>,tag1>,key'(i1,k1)).
euf M10. 

use H1.
exists j.

expand cond@R1(j).
use H3 with i1,k1.


fa 5. fa 6. 
fadup 4.
Qed.
