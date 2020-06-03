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
  try find k,i such that snd(x) = h(<<nR,fst(x)>,tag1>,diff(key(i),key'(i,k))) in
    out(cR,h(<<snd(x),nR>,tag2>,diff(key(i),key'(i,k))))
  else
    out(cR,ko)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).


equiv foo.
Proof.
induction t.
(* Case R *)
admit.

(* Case R1 *)
expand frame@R1(j,k,i).
expand exec@R1(j,k,i).
expand cond@R1(j,k,i).
(* HELP je trouve le changement d'indice k et i dans key perturbant *)

(* Case R2 *)
admit.
(* Case T *)
admit.
(* Case T1 *)
admit.
(* Case T2 *)
admit.
Qed.


