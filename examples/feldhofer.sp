(*******************************************************************************
FELDHOFER

[B] Martin Feldhofer, Sandra Dominikus, and Johannes Wolkerstorfer.
Strong authentication for RFID systems using the AES algorithm. In
Marc Joye and Jean-Jacques Quisquater, editors, Cryptographic Hard-
ware and Embedded Systems - CHES 2004: 6th International Workshop
Cambridge, MA, USA, August 11-13, 2004. Proceedings, volume 3156
of Lecture Notes in Computer Science, pages 357–370. Springer, 2004.

R --> T : nr
T --> R : enc(<nr,nt>,r,k), h(<nr,nt>,r,k)
R --> T : enc(<nt,nr>,r,k)

We assume here that the encryption used is an encrypt then mac,
such that the encryption is AE.

This is a "light" model without the last check of T.
*******************************************************************************)

channel cR
channel cT

name kE : message
name kbE : index-> message

name kH : message
name kbH : index-> message

hash h
senc enc,dec

name nr : index  -> message
name nt : index -> index -> message

name rt : index -> index -> message
name rr : index -> message

axiom dec :
  forall (m:message, r:message, key:message), dec(enc(m,r,key),key)  = m

process Reader(i:index) =
  out(cR, nr(i));
  in(cR, mess);
  if exists (j:index),
      h(fst(mess), diff(kH,kbH(j))) = snd(mess) &&
      fst(dec(fst(mess),  diff(kE,kbE(j)))) = nr(i)
  then
    out(cR,
      try find l,j such that
        h(fst(mess), diff(kH,kbH(j))) = snd(mess) &&
        fst(dec(fst(mess),  diff(kE,kbE(j)))) = nr(i)
      in
        enc(<snd(dec(fst(mess), diff(kE,kbE(j)))),nr(i)>, rr(i), diff(kE,kbE(j))))

process Tag(i:index, j:index) =
  in(cT, nR);
  let cypher = enc(<nR,nt(i,j)>, rt(i,j), diff(kE,kbE(j))) in
  out(cT, <cypher,h(cypher, diff(kH,kbH(j)) )> )

system (!_i Reader(i) | !_i !_j Tag(i,j)).

goal wa_Reader1 :
  forall (i:index),
    cond@Reader1(i)
    <=>
    (exists (l,k:index),
      Tag(l,k) < Reader1(i) && Reader(i) < Reader1(i)  &&
      output@Tag(l,k) = <fst(input@Reader1(i)),snd(input@Reader1(i))> &&
      input@Tag(l,k) = output@Reader(i)).
Proof.
  simpl.

  expand cond@Reader1(i).
  expand output@Reader(i).
  split.

  project.

  euf M0.
  exists i1,j1.
  depends Reader(i), Reader1(i).

  euf M0.
  exists i1,j.
  depends Reader(i), Reader1(i).

  exists k.
Qed.

goal [right] wa_Reader1_right :
  forall (i,j:index),
    (h(fst(input@Reader1(i)), kbH(j)) = snd(input@Reader1(i)) &&
    fst(dec(fst(input@Reader1(i)), kbE(j))) = nr(i)
    <=>
    exists (l:index),
    Tag(l,j) < Reader1(i) && Reader(i) < Reader1(i)  &&
    output@Tag(l,j) = <fst(input@Reader1(i)),snd(input@Reader1(i))> &&
    input@Tag(l,j) = output@Reader(i)).
Proof.
  simpl.
  euf M0.
  exists i1.
  depends Reader(i), Reader1(i).
Qed.

goal [left] wa_Reader1_left :
  forall (i:index),
  ( h(fst(input@Reader1(i)), kH) = snd(input@Reader1(i)) && fst(dec(fst(input@Reader1(i)),  kE)) = nr(i)
  <=>
  exists (l,j:index),
    Tag(l,j) < Reader1(i) && Reader(i) < Reader1(i)  &&
    output@Tag(l,j) = <fst(input@Reader1(i)),snd(input@Reader1(i))> &&
    input@Tag(l,j) = output@Reader(i)).
Proof.
  simpl.
  euf M0.
  exists i1,j.
  depends Reader(i), Reader1(i).
Qed.

goal wa_A :
  forall (i:index),
  (cond@A(i)
  <=>
  not (exists (l,k:index),
    Tag(l,k) < A(i) && Reader(i) < A(i)  &&
    output@Tag(l,k) = <fst(input@A(i)),snd(input@A(i))> &&
    input@Tag(l,k) = output@Reader(i))).
Proof.
  simpl.

  expand cond@A(i).
  expand output@Reader(i).
  split.

  project.
  notleft H0.

  apply H0 to l.
  case H1.

  notleft H0.
  apply H0 to k.
  case H1.

  notleft H0.
  project.
  euf M0.
  apply H0 to i1,j1.
  case H1.
  depends Reader(i), A(i).

  euf M0.
  apply H0 to i1,j.

  case H1.
  depends Reader(i), A(i).
Qed.

equiv unlinkability.
Proof.
  enrich seq(i->nr(i)). enrich seq(i,j->nt(i,j)).

  induction t.

  expand seq(i->nr(i)),i.
  expandall.
  fa 3.

  expand frame@Reader1(i). expand exec@Reader1(i).
  equivalent
    cond@Reader1(i),
    (exists (l,k:index),
      Tag(l,k) < Reader1(i) && Reader(i) < Reader1(i)  &&
      output@Tag(l,k) = <fst(input@Reader1(i)),snd(input@Reader1(i))> &&
      input@Tag(l,k) = output@Reader(i)).
  apply wa_Reader1 to i.
  expand output@Reader1(i).
  fa 2.

  equivalent
    (if
      (exec@pred(Reader1(i)) &&
       exists (l,k:index),
       (((Tag(l,k) < Reader1(i) && Reader(i) < Reader1(i)) &&
         output@Tag(l,k) = <fst(input@Reader1(i)),snd(input@Reader1(i))>)
        && input@Tag(l,k) = output@Reader(i)))
      then
      (try find l,j such that
         (h(fst(input@Reader1(i)),diff(kH,kbH(j))) = snd(input@Reader1(i)) &&
          fst(dec(fst(input@Reader1(i)),diff(kE,kbE(j)))) = nr(i))
         in
         enc(<snd(dec(fst(input@Reader1(i)),diff(kE,kbE(j)))),nr(i)>,rr(
             i),diff(kE,kbE(j))))),
    (if
      (exec@pred(Reader1(i)) &&
       exists (l,k:index),
       (((Tag(l,k) < Reader1(i) && Reader(i) < Reader1(i)) &&
         output@Tag(l,k) = <fst(input@Reader1(i)),snd(input@Reader1(i))>)
        && input@Tag(l,k) = output@Reader(i)))
      then
      (try find l,j such that
      (exec@pred(Reader1(i)) &&
       (((Tag(l,j) < Reader1(i) && Reader(i) < Reader1(i)) &&
         output@Tag(l,j) = <fst(input@Reader1(i)),snd(input@Reader1(i))>)
        && input@Tag(l,j) = output@Reader(i)))


         in
         enc(<nt(l,j),nr(i)>,rr(
             i),diff(kE,kbE(j))))).
  project.
  fa.
  apply wa_Reader1 to i.
  exists l,k.
  exists l,k.
  fa.
  exists l,k.
  fa.
  exists l,k.
  exists l,k.
  fa.
  apply wa_Reader1_right to i,j.
  apply H1.
  exists l2.
  fa 3.
  fadup 3.
  fa 3.
  fadup 3.
  fa 3.
  fadup 3.
  enckp 3.
  cca1 3.

  expand seq(i->nr(i)),i.
  expand seq(i,j->nt(i,j)),l,j.

  expand frame@A(i). expand exec@A(i).
  equivalent
    cond@A(i),
    not (exists (l,k:index),
      Tag(l,k) < A(i) && Reader(i) < A(i)  &&
      output@Tag(l,k) = <fst(input@A(i)),snd(input@A(i))> &&
      input@Tag(l,k) = output@Reader(i)).
  apply wa_A to i.

  fa 2. fa 3.
  fadup 3.
  fa 3.
  fadup 3.

  expandall.

  fa 2.
  fa 3.
  fa 3.
  fa 3.
  prf 4.

  yesif 4.
  project.
  assert snd( dec(fst(input@Reader1(i1)),kE)) =nt(i,j).
  fresh M1.
  assert snd( dec(fst(input@Reader1(i1)),kbE(j))) =nt(i,j).
  fresh M1.

  enckp 3.
  cca1 3.
  fa 3.
  fa 3.
  expand seq(i,j->nt(i,j)),i,j.
  fresh 4.
Qed.
