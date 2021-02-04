(*******************************************************************************
FELDHOFER

[B] Martin Feldhofer, Sandra Dominikus, and Johannes Wolkerstorfer.
Strong authentication for RFID systems using the AES algorithm. In
Marc Joye and Jean-Jacques Quisquater, editors, Cryptographic Hard-
ware and Embedded Systems - CHES 2004: 6th International Workshop
Cambridge, MA, USA, August 11-13, 2004. Proceedings, volume 3156
of Lecture Notes in Computer Science, pages 357–370. Springer, 2004.

R --> T : nr
T --> R : enc(<tagT,<nr,nt>>,rt,k)
R --> T : enc(<tagR,<nt,nr>>,rr,k)

We replace the AES algorithm of the original protocol by a randomized
symmetric encryption, the closest primitive currently supported in
Squirrel. The encryption is assumed to be authenticated, e.g. using the
encrypt-then-mac paradigm. Specifically, we make use of the crypto
assumptions INT-CTXT and ENC-KP on our symmetric encryption.

We add tags for simplicity, and conjecture that the results hold
for the protocol without tags, though at the cost of a proof by
induction for wa_* goals.

This is a "light" model without the last check of T.
*******************************************************************************)

channel cR
channel cT

name kE : index -> message
name kbE : index -> index -> message

(** Fresh key used for ENC-KP applications. *)
name k_fresh : message

senc enc,dec

abstract tagR : message
abstract tagT : message

name nr : index  -> message
name nt : index -> index -> message

name rt : index -> index -> message
name rr : index -> message

abstract ok : message
abstract ko : message

process Reader(k:index) =
  out(cR, nr(k));
  in(cR, mess);
  if exists (i,j:index),
      dec(mess, diff(kE(i),kbE(i,j))) <> fail &&
      fst(dec(mess, diff(kE(i),kbE(i,j)))) = tagT &&
      fst(snd(dec(mess, diff(kE(i),kbE(i,j))))) = nr(k)
  then
    out(cR,
      try find i,j such that
        dec(mess, diff(kE(i),kbE(i,j))) <> fail &&
        fst(dec(mess, diff(kE(i),kbE(i,j)))) = tagT &&
        fst(snd(dec(mess, diff(kE(i),kbE(i,j))))) = nr(k)
      in
        enc(<tagR,<snd(snd(dec(mess, diff(kE(i),kbE(i,j))))),nr(k)>>, rr(k),
            diff(kE(i),kbE(i,j)))).

process Tag(i:index, j:index) =
  in(cT, nR);
  let cipher = enc(<tagT,<nR,nt(i,j)>>, rt(i,j), diff(kE(i),kbE(i,j))) in
  out(cT, cipher).

system (!_k Reader(k) | !_i !_j Tag(i,j)).

axiom tags_neq : tagR <> tagT

axiom fail_not_pair : forall (x,y:message), fail <> <x,y>.

goal wa_Reader1 :
  forall (k:index),
    exec@Reader1(k)
    <=>
    exec@pred(Reader1(k)) && (exists (i,j:index),
      Tag(i,j) < Reader1(k) && Reader(k) < Reader1(k)  &&
      output@Tag(i,j) = input@Reader1(k) &&
      input@Tag(i,j) = output@Reader(k)).
Proof.
  intro *.
  expand exec@Reader1(k).
  expand cond@Reader1(k).
  expand output@Reader(k).
  split.

  project; apply tags_neq.

  (* First projection. *)
  intctxt Mneq.
  exists i, j1.
  by depends Reader(k), Reader1(k).

  (* Second projection. *)
  intctxt Mneq.
  exists i,j.
  by depends Reader(k), Reader1(k).

  (* Direction <= *)
  exists i,j.
  by apply fail_not_pair to tagT, <input@Tag(i,j),nt(i,j)>.
Qed.

(* Action Reader2 is the empty else branch of the reader. *)
goal wa_Reader2 :
  forall (k:index),
    exec@Reader2(k)
    <=>
    exec@pred(Reader2(k)) && not (exists (i,j:index),
      Tag(i,j) < Reader2(k) && Reader(k) < Reader2(k)  &&
      output@Tag(i,j) = input@Reader2(k) &&
      input@Tag(i,j) = output@Reader(k)).
Proof.
  intro *.
  expand exec@Reader2(k).
  expand cond@Reader2(k).
  expand output@Reader(k).
  split.

  (* Direction => is the obvious one *)

  notleft H0.
  apply H0 to i,j; case H1.
  by apply fail_not_pair to tagT, <input@Tag(i,j), nt(i,j)>.

  (* Direction <= *)

  notleft H0.
  apply tags_neq.
  project.

  intctxt Mneq.
  apply H0 to i,j1; case H1.
  by depends Reader(k),Reader2(k).

  intctxt Mneq.
  apply H0 to i,j; case H1.
  by depends Reader(k),Reader2(k).
Qed.

goal lemma : forall (i,j,i1,j1:index),
  output@Tag(i,j) = output@Tag(i1,j1) => i = i1 && j = j1.
Proof.
  intro *.
  project. 

  assert dec(output@Tag(i,j),kE(i1)) = <tagT,<input@Tag(i1,j1),nt(i1,j1)>>.
  intctxt HA.
  case H.
  assert dec(output@Tag(i1,j1),kE(i)) = <tagT,<input@Tag(i,j),nt(i,j)>>.
  intctxt HA0.
  by case H0.
  by apply fail_not_pair to tagT,<input@Tag(i,j),nt(i,j)>.
  by apply fail_not_pair to tagT,<input@Tag(i1,j1),nt(i1,j1)>.

  assert dec(output@Tag(i,j),kbE(i1,j1)) = <tagT,<input@Tag(i1,j1),nt(i1,j1)>>.
  intctxt HA.
  case H.
  assert dec(output@Tag(i1,j1),kbE(i,j)) = <tagT,<input@Tag(i,j),nt(i,j)>>.
  intctxt HA0.
  by case H0.
  by apply fail_not_pair to tagT,<input@Tag(i,j),nt(i,j)>.
  by apply fail_not_pair to tagT,<input@Tag(i1,j1),nt(i1,j1)>.
Qed.

equiv unlinkability.
Proof.
  enrich seq(k->nr(k)). enrich seq(i,j->nt(i,j)).

  induction t.

  (* Action 1/4: Reader *)

  expand seq(k->nr(k)),k.
  expandall.
  by fa 3.

  (* Action 2/4: Reader1 *)

  expand frame@Reader1(k).
  equivalent
    exec@Reader1(k),
    exec@pred(Reader1(k)) &&
    exists (i,j:index),
      Tag(i,j) < Reader1(k) && Reader(k) < Reader1(k)  &&
      output@Tag(i,j) = input@Reader1(k) &&
      input@Tag(i,j) = output@Reader(k).
  by apply wa_Reader1 to k.

  expand output@Reader1(k).
  fa 2. fa 3. fadup 3.

  equivalent
    (if
       exec@pred(Reader1(k)) &&
       (exists (i,j:index),
         ((Tag(i,j) < Reader1(k) &&
           Reader(k) < Reader1(k)) &&
          output@Tag(i,j) = input@Reader1(k)) &&
         input@Tag(i,j) = output@Reader(k))
     then
       (try find i,j such that
          (dec(input@Reader1(k),diff(kE(i),kbE(i,j))) <> fail &&
           fst(dec(input@Reader1(k),diff(kE(i),kbE(i,j)))) = tagT) &&
          fst(snd(dec(input@Reader1(k),diff(kE(i),kbE(i,j))))) = nr(k)
        in
          enc(<tagR,<snd(snd(dec(input@Reader1(k),diff(kE(i),kbE(i,j))))),
                     nr(k)>>,
              rr(k),
              diff(kE(i),kbE(i,j))))),
    (if
       exec@pred(Reader1(k)) &&
       (exists (i,j:index),
         ((Tag(i,j) < Reader1(k) &&
           Reader(k) < Reader1(k)) &&
          output@Tag(i,j) = input@Reader1(k)) &&
         input@Tag(i,j) = output@Reader(k))
     then
       (try find i,j such that
          exec@pred(Reader1(k)) &&
          (Tag(i,j) < Reader1(k) &&
           Reader(k) < Reader1(k) &&
           output@Tag(i,j) = input@Reader1(k) &&
           input@Tag(i,j) = output@Reader(k))
        in
          enc(<tagR,<nt(i,j),nr(k)>>,rr(k),
              diff(kE(i),kbE(i,j))))).
  fa. 
  by exists i,j.
  by exists i,j.
  project.

  fa.
  (* find condA => condB *)
  intctxt Mneq.
  by apply tags_neq.
  by exists j2.

  (* find condB => condA *)
  apply lemma to i,j,i1,j1.
  by apply fail_not_pair to tagT, <input@Tag(i,j),nt(i,j)>.

  fa.
  (* find condA => condB *)
  intctxt Mneq.
  by apply tags_neq.
  (* find condB => condA *)
  apply lemma to i,j,i1,j1.
  by apply fail_not_pair to tagT, <input@Tag(i,j),nt(i,j)>.

  fa 3; fadup 3.
  fa 3; fadup 3.
  enckp 3, k_fresh.
  expand seq(k->nr(k)),k.
  expand seq(i,j->nt(i,j)),i,j.
  fa 5.
  fresh 6.
  by fresh 5; yesif 5.

  (* Action 3/4: Reader2 *)

  expand frame@Reader2(k).

  equivalent
    exec@Reader2(k),
    exec@pred(Reader2(k)) && not (exists (i,j:index),
      Tag(i,j) < Reader2(k) && Reader(k) < Reader2(k)  &&
      output@Tag(i,j) = input@Reader2(k) &&
      input@Tag(i,j) = output@Reader(k)).
  by apply wa_Reader2 to k.

  fa 2.
  fa 3; fadup 3.
  by fa 3; fadup 3.

  (* Action 4/4: Tag *)

  expandall.
  fa 2. fa 3.  fa 3.

  enckp 3, k_fresh.
  expand seq(i,j->nt(i,j)),i,j.
  fa 4.
  fresh 5.
  by fresh 4; yesif 4.
Qed.
