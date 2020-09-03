(*******************************************************************************
LAK (WITH PAIRS)

[D] Lucca Hirschi, David Baelde, and Stéphanie Delaune. A method for
unbounded verification of privacy-type properties. Journal of Computer
Security, 27(3):277–342, 2019.

R --> T : nR
T --> R : <nT,h(<<nR,nT>,tag1>,kT)>
R --> T : h(<<h(<<nR,nT>,tag1>,kT),nR>,tag2>,kR)

We consider tags in the messages (tag1 and tag2) to ease the proof.

This is a "light" model without the last check of T.
*******************************************************************************)

hash h

abstract ok : message
abstract ko : message

abstract tag1 : message
abstract tag2 : message
axiom tags_neq : tag1 <> tag2

name key : index->message
name key': index->index->message

channel cT
channel cR

process tag(i:index,k:index) =
  new nT;
  in(cR,nR);
  let m2 = h(<<nR,nT>,tag1>,diff(key(i),key'(i,k))) in
  out(cT,<nT,m2>)

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
  cond@R1(j)
  <=>
  (exists (i,k:index),
    T(i,k) < R1(j) && R(j) < T(i,k) &&
    snd(output@T(i,k)) = snd(input@R1(j)) &&
    fst(output@T(i,k)) = fst(input@R1(j)) &&
    input@T(i,k) = output@R(j)).

Proof.
  intros.
  expand cond@R1(j).
  split.

  (* COND => WA *)
  apply tags_neq; project.
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

  (* WA => COND *)
  exists i,k.
Qed.

goal wa_R2: forall j:index,
  cond@R2(j)
  <=>
  (not(exists (i,k:index),
    T(i,k) < R2(j) && R(j) < T(i,k) &&
    snd(output@T(i,k)) = snd(input@R2(j)) &&
    fst(output@T(i,k)) = fst(input@R2(j)) &&
    input@T(i,k) = output@R(j))).

Proof.
  intros.
  expand cond@R2(j).
  split.

  (* WA => COND *)
  apply H0.
  exists i,k.
  apply H0.

  (* COND => WA *)
  apply tags_neq; project.
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
Qed.

goal [left] wa_R1_left:
  forall (i,j:index),
    (snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key(i)))
    <=>
    (exists k:index,
    T(i,k) < R1(j) && R(j) < T(i,k) &&
    snd(output@T(i,k)) = snd(input@R1(j)) &&
    fst(output@T(i,k)) = fst(input@R1(j)) &&
    input@T(i,k) = output@R(j)).

Proof.
  intros.
  apply tags_neq.
  euf M0.
  exists k.
  assert input@T(i,k)=nR(j).
  fresh M3.
  depends R(j),R2(j).
Qed.

goal [right] wa_R1_right:
  forall (i,j,k:index),
    (snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k)))
    <=>
    (T(i,k) < R1(j) && R(j) < T(i,k) &&
    snd(output@T(i,k)) = snd(input@R1(j)) &&
    fst(output@T(i,k)) = fst(input@R1(j)) &&
    input@T(i,k) = output@R(j)).

Proof.
  intros.
  apply tags_neq.
  euf M0.
  assert input@T(i,k)=nR(j).
  fresh M3.
  depends R(j),R2(j).
Qed.


equiv unlinkability.
Proof.
  induction t.

  (* Case R *)
  expand frame@R(j); expand exec@R(j).
  expand cond@R(j); expand output@R(j).
  fa 0; fa 1; fa 1.
  fresh 1; yesif 1.
  repeat split.
  depends R(j),R2(j).
  depends R(j),R1(j).

  (* Case R1 *)
  expand frame@R1(j); expand exec@R1(j).
  expand output@R1(j).
  fa 0; fa 1.

  equivalent
    cond@R1(j),
    (exists (i,k:index),
      T(i,k) < R1(j) && R(j) < T(i,k) &&
      snd(output@T(i,k)) = snd(input@R1(j)) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      input@T(i,k) = output@R(j)).
  apply wa_R1 to j.

  equivalent
    (if exec@pred(R1(j)) &&
        exists (i,k:index),
        (((T(i,k) < R1(j) && R(j) < T(i,k) && snd(output@T(i,k)) = snd(input@R1(j))) &&
        fst(output@T(i,k)) = fst(input@R1(j))) &&
        input@T(i,k) = output@R(j))
     then (try find i,k such that
             snd(input@R1(j)) =
             h(<<nR(j),fst(input@R1(j))>,tag1>,diff(key(i),key'(i,k)))
           in
             h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k))))),
    (if exec@pred(R1(j)) &&
        exists (i,k:index),
        (T(i,k) < R1(j) && R(j) < T(i,k) && snd(output@T(i,k)) = snd(input@R1(j)) &&
        fst(output@T(i,k)) = fst(input@R1(j)) &&
        input@T(i,k) = output@R(j))
     then (try find i,k such that
            (exec@pred(R1(j)) &&
  	   (T(i,k) < R1(j) && snd(output@T(i,k)) = snd(input@R1(j)) &&
  	    fst(output@T(i,k)) = fst(input@R1(j)) &&
  	    R(j) < T(i,k) && input@T(i,k) = output@R(j)))
           in
  	   if exec@pred(R1(j))
  	   then h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k))))).
  fa.
  exists i,k. exists i,k.
  project.
  (* LEFT *)
  fa.
  apply wa_R1_left to i1,j.
  apply H1.
  exists k.
  yesif.
  (* RIGHT *)
  fa.
  apply wa_R1_right to i1,j,k1.
  apply H1.
  yesif.

  fa 2. fadup 1.
  fa 1. fadup 1.
  prf 1.
  ifcond 1, exec@pred(R1(j)).
  fa 1.
  yesif 1.
  apply tags_neq; project.
  fresh 1.

  (* Case R2 *)
  expand frame@R2(j); expand exec@R2(j).
  expand output@R2(j).
  fa 0; fa 1.
  equivalent
    cond@R2(j),
    (not(exists (i,k:index),
      T(i,k) < R2(j) && R(j) < T(i,k) &&
      snd(output@T(i,k)) = snd(input@R2(j)) &&
      fst(output@T(i,k)) = fst(input@R2(j)) &&
      input@T(i,k) = output@R(j))).
  apply wa_R2 to j.
  fadup 1.

  (* Case T *)
  expand frame@T(i,k); expand exec@T(i,k).
  expand cond@T(i,k); expand output@T(i,k).
  expand m2(i,k)@T(i,k).
  fa 0. fa 1. fa 1. fa 1.
  prf 2.
  yesif 2.
  apply tags_neq; project.
  assert fst(input@R1(j))=nT(i,k).
  fresh M2.
  assert fst(input@R1(j))=nT(i,k).
  fresh M2.
  fresh 2.
  fresh 1. yesif 1.

Qed.