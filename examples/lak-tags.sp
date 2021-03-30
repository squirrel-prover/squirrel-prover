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

axiom tags_neq : tag1 <> tag2.

goal wa_R1 (j:index):
  happens(R1(j)) =>
    (cond@R1(j)
     <=>
     (exists (i,k:index),
       T(i,k) < R1(j) && R(j) < T(i,k) &&
       snd(output@T(i,k)) = snd(input@R1(j)) &&
       fst(output@T(i,k)) = fst(input@R1(j)) &&
       input@T(i,k) = output@R(j))).
Proof.
  intro *.
  expand cond.
  split.

  (* COND => WA *)
  use tags_neq; project.
  (* LEFT *)
  euf Meq.
  exists i,k0.
  assert input@T(i,k0)=nR(j).
  fresh Meq1.
  by case H; depends R(j),R2(j).

  (* RIGHT *)
  euf Meq.
  exists i,k.
  assert input@T(i,k)=nR(j).
  fresh Meq1.
  by case H; depends R(j),R2(j).

  (* WA => COND *)
  by exists i,k.
Qed.

goal wa_R2 (j:index):
  happens(R2(j)) =>
   (cond@R2(j)
    <=>
    (not(exists (i,k:index),
      T(i,k) < R2(j) && R(j) < T(i,k) &&
      snd(output@T(i,k)) = snd(input@R2(j)) &&
      fst(output@T(i,k)) = fst(input@R2(j)) &&
      input@T(i,k) = output@R(j)))).
Proof.
  intro *.
  expand cond.
  split.

  (* WA => COND *)
  use H.
  by exists i,k.

  (* COND => WA *)
  use H.
  use tags_neq; project.
  (* LEFT *) 
  euf Meq.
  exists i,k0.
  assert input@T(i,k0)=nR(j).
  fresh Meq1.
  by case H0; depends R(j),R1(j).

  (* RIGHT *)
  euf Meq.
  exists i,k.
  assert input@T(i,k)=nR(j).
  fresh Meq1.
  by case H0; depends R(j),R1(j).
Qed.

goal [left] wa_R1_left (i,j:index):
  happens(R1(j)) =>
    ((snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key(i)))
     <=>
     (exists k:index,
     T(i,k) < R1(j) && R(j) < T(i,k) &&
     snd(output@T(i,k)) = snd(input@R1(j)) &&
     fst(output@T(i,k)) = fst(input@R1(j)) &&
     input@T(i,k) = output@R(j))).
Proof.
  intro *.
  use tags_neq.
  euf Meq.
  exists k.
  assert input@T(i,k)=nR(j).
  fresh Meq1.
  by case H; depends R(j),R2(j).
Qed.

goal [right] wa_R1_right (i,j,k:index):
  happens(R1(j)) =>
    ((snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k)))
     <=>
     (T(i,k) < R1(j) && R(j) < T(i,k) &&
     snd(output@T(i,k)) = snd(input@R1(j)) &&
     fst(output@T(i,k)) = fst(input@R1(j)) &&
     input@T(i,k) = output@R(j))).
Proof.
  intro *.
  use tags_neq.
  euf Meq.
  assert input@T(i,k)=nR(j).
  fresh Meq1.
  by case H; depends R(j),R2(j).
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
  by depends R(j0),R1(j0).
  by depends R(j0),R2(j0).

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
  by use wa_R1 with j.

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
  by exists i,k. by exists i,k.
  project.

  (* LEFT *)
  fa.
  use wa_R1_left with i0,j.
  use H1.
  by exists k. 

  yesif.
  (* RIGHT *)
  fa.
  use wa_R1_right with i0,j,k0.
  by use H1.
  by yesif.

  fa 2; fadup 1.
  fa 1; fadup 1.
  prf 1.
  ifcond 1, exec@pred(R1(j)).
  fa 1.
  yesif 1.
  by use tags_neq; project.
  by fresh 1.

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
  by use wa_R2 with j.
  by fadup 1.

  (* Case T *)
  expand frame@T(i,k); expand exec@T(i,k).
  expand cond@T(i,k); expand output@T(i,k).
  expand m2(i,k)@T(i,k).
  fa 0. fa 1. fa 1. fa 1.
  prf 2.
  yesif 2.
  use tags_neq; project.
  split.
  assert fst(input@R2(j))=nT(i,k); by fresh Meq0.
  split.
  assert fst(input@R1(j))=nT(i,k); by fresh Meq0.
  assert fst(input@R1(j))=nT(i,k); by fresh Meq0.
  split.
  split.  
  assert fst(input@R1(j))=nT(i,k); by fresh Meq0.
  assert fst(input@R1(j))=nT(i,k); by fresh Meq0.
  assert fst(input@R2(j))=nT(i,k); by fresh Meq0.
  fresh 2.
  by fresh 1; yesif 1.
Qed.
