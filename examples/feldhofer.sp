(*******************************************************************************
FELDHOFER

[B] Martin Feldhofer, Sandra Dominikus, and Johannes Wolkerstorfer.
Strong authentication for RFID systems using the AES algorithm. In
Marc Joye and Jean-Jacques Quisquater, editors, Cryptographic Hard-
ware and Embedded Systems - CHES 2004: 6th International Workshop
Cambridge, MA, USA, August 11-13, 2004. Proceedings, volume 3156
of Lecture Notes in Computer Science, pages 357–370. Springer, 2004.

R --> T : nr
T --> R : enc(<nr,nt>,r,k)
R --> T : enc(<nt,nr>,r,k)

We assume here that the encryption used is an encrypt then mac,
such that the encryption is AE. In particular, it is IND-CCA1,
and INT-CTXT.

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

abstract ok : message
abstract ko : message

axiom cor_enc :
  forall (m,r,key,skey:message), (dec(enc(m,r,key),skey) = fail || key=skey)

axiom fail_not_pair : forall (x,y:message), fail <> <x,y>

process Reader(i:index) =
  out(cR, nr(i));
  in(cR, mess);
  if exists (j:index),
      dec(mess,  diff(kE,kbE(j)) ) <> fail
      &&
      fst(dec(mess,  diff(kE,kbE(j)) )) = nr(i)
  then
    out(cR,
      try find l,j such that
        dec(mess,  diff(kE,kbE(j)) ) <> fail
        &&
        fst(dec(mess,  diff(kE,kbE(j)))) = nr(i)
      in
        enc(<snd(dec(mess, diff(kE,kbE(j)))),nr(i)>, rr(i), diff(kE,kbE(j))))

process Tag(i:index, j:index) =
  in(cT, nR);
  let cypher = enc(<nR,nt(i,j)>, rt(i,j), diff(kE,kbE(j))) in
  out(cT, cypher )


system (!_i Reader(i) | !_i !_j Tag(i,j)).

goal wa_Reader1 :
  forall (i:index),
    exec@Reader1(i)
    <=>
    exec@pred(Reader1(i)) && (exists (l,k:index),
      Tag(l,k) < Reader1(i) && Reader(i) < Reader1(i)  &&
      output@Tag(l,k) = input@Reader1(i) &&
      input@Tag(l,k) = output@Reader(i)).
Proof.
  simpl.
  expand exec@Reader1(i).
  expand cond@Reader1(i).
  expand output@Reader(i).
  split.

  project.

  (* First projection. *)
  intctxt M0.
  (* Here, the reader has actually been given the output produced by a reader... *)
  executable pred(Reader1(i)).
  apply H1 to Reader1(i1).
  expand exec@Reader1(i1).
  expand cond@Reader1(i1).
  (* We use intctxt once again, to conclude that it is not possible to satisfy then the conditions.*)
  intctxt M3.
  simpl.

  (* Here, it is the honest case, so easy to conclude. *)
  exists i1, j1.
  depends Reader(i), Reader1(i).

  (* Second projection. *)
  intctxt M0.

  (* Here, the reader has actually been given the output produced by a reader... *)
  executable pred(Reader1(i)).
  apply H1 to Reader1(i1).
  expand exec@Reader1(i1).
  expand cond@Reader1(i1).


  (* We use intctxt once again, to conclude that it is not possible to satisfy XXX then the conditions.*)
  intctxt M3.

  apply cor_enc to <snd(dec(input@Reader1(i2),kbE(j1))),nr(i2)>, rr(i2), kbE(j1), kbE(j).
  case H3.
  assert snd(fail) <> nr(i).

  apply cor_enc to <input@Tag(i2,j1),nt(i2,j1)>,rt(i2,j1), kbE(j1), kbE(j).
  case H3.
  assert snd(fail) <> nr(i).
  simpl.

  exists i1,j.
  depends Reader(i), Reader1(i).

  exists k.
  apply fail_not_pair to input@Tag(l,k),nt(l,k).

Qed.


goal wa_A :
  forall (i:index),
    exec@A(i)
    <=>
    exec@pred(A(i)) && not (exists (l,k:index),
      Tag(l,k) < A(i) && Reader(i) < A(i)  &&
      output@Tag(l,k) = input@A(i) &&
      input@Tag(l,k) = output@Reader(i)).
Proof.
  simpl.
  expand exec@A(i).
  expand cond@A(i).
  expand output@Reader(i).
  split.
  notleft H1.
  project.

  apply H1 to i.
  case H2.
  apply fail_not_pair to input@Tag(l,k), nt(l,k).

  apply H1 to k.
  case H2.
  apply fail_not_pair to input@Tag(l,k), nt(l,k).

  notleft H1.

  project.
  intctxt M0.

  executable pred(A(i)).
  apply H2 to Reader1(i1).
  expand exec@Reader1(i1).
  expand cond@Reader1(i1).

  intctxt M3.
  apply H2 to Reader1(i).
  expand exec@Reader1(i).
  expand cond@Reader1(i).
  intctxt M6.

  apply H1 to i1,j1.
  case H2.
  depends Reader(i), A(i).

  intctxt M0.

  executable pred(A(i)).
  apply H2 to Reader1(i1).
  expand exec@Reader1(i1).
  expand cond@Reader1(i1).

  intctxt M3.

  apply cor_enc to <snd(dec(input@Reader1(i2),kbE(j1))),nr(i2)>, rr(i2), kbE(j1), kbE(j).
  case H4.
  assert snd(fail) <> nr(i).
  apply H2 to Reader1(i).
  expand exec@Reader1(i).
  expand cond@Reader1(i).

  intctxt M6.

  apply cor_enc to <snd(dec(input@Reader1(i2),kbE(j1))),nr(i2)>, rr(i2), kbE(j1), kbE(j).
  case H5.

  assert snd(fail) <> nr(i).

  apply H1 to i2,j1.
  case H5.

  depends Reader(i), A(i).

  apply cor_enc to <input@Tag(i2,j1),nt(i2,j1)>,rt(i2,j1),kbE(j1),kbE(j).
  case H5.
  assert snd(fail) <> nr(i).

  apply cor_enc to <input@Tag(i2,j1),nt(i2,j1)>,rt(i2,j1),kbE(j1),kbE(j).

  case H4.
  assert snd(fail) <> nr(i).

  apply H1 to i1,j.
  case H2.

  depends Reader(i), A(i).

Qed.

equiv unlinkability.
Proof.
  enrich seq(i->nr(i)). enrich seq(i,j->nt(i,j)).

  induction t.

  expand seq(i->nr(i)),i.
  expandall.
  fa 3.

  expand frame@Reader1(i).
  equivalent exec@Reader1(i),
  exec@pred(Reader1(i)) && (exists (l,k:index),
      Tag(l,k) < Reader1(i) && Reader(i) < Reader1(i)  &&
      output@Tag(l,k) = input@Reader1(i) &&
      input@Tag(l,k) = output@Reader(i)).

  apply wa_Reader1 to i.

  expand output@Reader1(i).
  fa 2.

  equivalent
  (if
        exec@pred(Reader1(i)) &&  exists (l,k:index),
       ((((Tag(l,k) < Reader1(i)) &&
          Reader(i) < Reader1(i))
         && output@Tag(l,k) = input@Reader1(i))
        && input@Tag(l,k) = output@Reader(i))
       then
       (try find l,j such that
          (dec(input@Reader1(i),diff(kE,kbE(j))) <> fail &&
           fst(dec(input@Reader1(i),diff(kE,kbE(j)))) = nr(i))
          in
          enc(<snd(dec(input@Reader1(i),diff(kE,kbE(j)))),nr(i)>,rr(i),
              diff(kE,kbE(j))))),
  (if
      exec@pred(Reader1(i)) &&  exists (l,k:index),
       ((((Tag(l,k) < Reader1(i)) &&
          Reader(i) < Reader1(i))
         && output@Tag(l,k) = input@Reader1(i))
        && input@Tag(l,k) = output@Reader(i))
       then
       (try find l,j such that
           exec@pred(Reader1(i)) && (((( Tag(l,j) < Reader1(i)) &&
          Reader(i) < Reader1(i))
         && output@Tag(l,j) = input@Reader1(i))
        && input@Tag(l,j) = output@Reader(i))
          in
          enc(<nt(l,j),nr(i)>,rr(i),
              diff(kE,kbE(j))))).
  fa.

  exists l,k.
  exists l,k.
  project.
  fa.
  exists l,k.
  apply fail_not_pair to input@Tag(l,j), nt(l,j).

  fa.
  exists l.
  apply cor_enc to <input@Tag(l,k),nt(l,k)>,rt(l,k),kbE(k),kbE(j).
  case H1.

  apply fail_not_pair to input@Tag(l1,j), nt(l1,j).

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

  expand frame@A(i).

  equivalent
    exec@A(i),
    exec@pred(A(i)) &&not (exists (l,k:index),
      Tag(l,k) < A(i) && Reader(i) < A(i)  &&
      output@Tag(l,k) = input@A(i) &&
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

  enckp 3.
  cca1 3.
  fa 3.
  fa 3.
  expand seq(i,j->nt(i,j)),i,j.
Qed.
