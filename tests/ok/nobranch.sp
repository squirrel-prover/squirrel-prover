(** Regression test, for not branching tactic bug.
    The first tactic was looping, with a ill-defined not_branching function.
 *)


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


goal test :
forall (i,k:index),
(
(((((forall (i1,k1:index),
     ((T(i1,k1) < T(i,k) || T(i1,k1) <= T(i,k)) =>
      (i = i1 =>
       <<((input@T(i,k))),nT(i,k)>,tag1> <>
       <<input@T(i1,k1),nT(i1,k1)>,tag1>))
     &&
     forall (i1,k1:index),
     ((T1(i1,k1) < T(i,k) || T1(i1,k1) <= T(i,k)) =>
      ((i = i1 =>
        <<((input@T(i,k))),nT(i,k)>,tag1> <>
        <<input@T(i1,k1),nT(i1,k1)>,tag1>)
       &&
       (i = i1 =>
        <<((input@T(i,k))),nT(i,k)>,tag1> <>
        <<m2(i1,k1)@T1(i1,k1),input@T(i1,k1)>,tag2>))))
    &&
    forall (j,i1:index),
    ((R2(j) < T(i,k) || R2(j) <= T(i,k)) =>
     (i = i1 =>
      <<((input@T(i,k))),nT(i,k)>,tag1> <>
      <<nR(j),fst(input@R2(j))>,tag1>)))
   &&
   forall (j,i1,k1:index),
   ((R1(j,k1,i1) < T(i,k) || R1(j,k1,i1) <= T(i,k)) =>
    ((i = i1 =>
      <<((input@T(i,k))),nT(i,k)>,tag1> <>
      <<snd(input@R1(j,i1,k1)),nR(j)>,tag2>)
     &&
     (i = i1 =>
      <<((input@T(i,k))),nT(i,k)>,tag1> <>
      <<nR(j),fst(input@R1(j,i1,k1))>,tag1>))))
  &&
  forall (i1,k1:index),
  ((T2(i1,k1) < T(i,k) || T2(i1,k1) <= T(i,k)) =>
   ((i = i1 =>
     <<((input@T(i,k))),nT(i,k)>,tag1> <>
     <<input@T(i1,k1),nT(i1,k1)>,tag1>)
    &&
    (i = i1 =>
     <<((input@T(i,k))),nT(i,k)>,tag1> <>
     <<m2(i1,k1)@T2(i1,k1),input@T(i1,k1)>,tag2>))))
 &&
 ((((forall (i1,k1:index),
     ((T(i1,k1) < T(i,k) || T(i1,k1) <= T(i,k)) =>
      ((i = i1 && k = k1) =>
       <<((input@T(i,k))),nT(i,k)>,tag1> <>
       <<input@T(i1,k1),nT(i1,k1)>,tag1>))
     &&
     forall (i1,k1:index),
     ((T1(i1,k1) < T(i,k) || T1(i1,k1) <= T(i,k)) =>
      (((i = i1 && k = k1) =>
        <<((input@T(i,k))),nT(i,k)>,tag1> <>
        <<input@T(i1,k1),nT(i1,k1)>,tag1>)
       &&
       ((i = i1 && k = k1) =>
        <<((input@T(i,k))),nT(i,k)>,tag1> <>
        <<m2(i1,k1)@T1(i1,k1),input@T(i1,k1)>,tag2>))))
    &&
    forall (j,i1,k1:index),
    ((R2(j) < T(i,k) || R2(j) <= T(i,k)) =>
     ((i = i1 && k = k1) =>
      <<((input@T(i,k))),nT(i,k)>,tag1> <>
      <<nR(j),fst(input@R2(j))>,tag1>)))
   &&
   forall (j,i1,k1:index),
   ((R1(j,k1,i1) < T(i,k) || R1(j,k1,i1) <= T(i,k)) =>
    (((i = i1 && k = k1) =>
      <<((input@T(i,k))),nT(i,k)>,tag1> <>
      <<snd(input@R1(j,i1,k1)),nR(j)>,tag2>)
     &&
     ((i = i1 && k = k1) =>
      <<((input@T(i,k))),nT(i,k)>,tag1> <>
      <<nR(j),fst(input@R1(j,i1,k1))>,tag1>))))
  &&
  forall (i1,k1:index),
  ((T2(i1,k1) < T(i,k) || T2(i1,k1) <= T(i,k)) =>
   (((i = i1 && k = k1) =>
     <<((input@T(i,k))),nT(i,k)>,tag1> <>
     <<input@T(i1,k1),nT(i1,k1)>,tag1>)
    &&
    ((i = i1 && k = k1) =>
     <<((input@T(i,k))),nT(i,k)>,tag1> <>
     <<m2(i1,k1)@T2(i1,k1),input@T(i1,k1)>,tag2>)))))
).
Proof.
nosimpl(
try ((nobranch ((repeat ((split + intro )))
      ))))
.
admit.
Qed.
