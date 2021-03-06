(* R --> T: nr                                    *)
(* T --> R: nT, h(<nR, nT, tag1>, k)              *)
(* R --> T: h(<h(<nR, nT, tag2>, k), nr, ** nt **, tag2>,k) *)


(* Attention !! j'ai simplifie les raisonnement en ajoutant nt dans le dernier message *)
(* S.D.: je n'ai pas encore bien compris pourquoi ca m'aide mais sans cet ajout, *)
(* je me retrouve avec nt(i,k) et aussi nt(i,k1) car pour deduire que 2 hash egaux ont *)
(* leur composantes egales, je n'ai pas d'autres choix que euf, et du coup cela ne me *)
(* permet pas dedure facilement l'egalite que j'ai ici *)

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
  if m3 = h(<<h(<<nR,nT>,tag1>,key(i)),<nR,nT>>,tag2>,key(i)) then
    out(cT,ok)
  else
    out(cT,ko)

process reader(j:index) =
  new nR;
  out(cR,nR);
  in(cT,x);
  try find i such that snd(x) = h(<<nR,fst(x)>,tag1>,key(i)) in
    out(cR,h(<<snd(x),<nR,fst(x)>>,tag2>,key(i)))
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
exists j.
case H1.
repeat split.

assert (fst(input@R1(j,i)) = nT(i,k)).
fresh M3.
depends T(i,k), T2(i,k).

assert (input@T(i,k) = nR(j)).
fresh M3.
depends R(j), R2(j).
depends R(j), R1(j,i1).

repeat split.
depends T(i,k), T1(i,k).
assert (fst(input@R1(j,i)) = nT(i,k)).
fresh M3.
depends T(i,k), T1(i,k).
depends T(i,k), T2(i,k).
depends R(j), R1(j,i).
Qed.
