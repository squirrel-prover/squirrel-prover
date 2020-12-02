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

axiom tags_neq : tagR <> tagT

name nr : index  -> message
name nt : index -> index -> message

name rt : index -> index -> message
name rr : index -> message

abstract ok : message
abstract ko : message

axiom fail_not_pair : forall (x,y:message), fail <> <x,y>

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
            diff(kE(i),kbE(i,j))))

process Tag(i:index, j:index) =
  in(cT, nR);
  let cypher = enc(<tagT,<nR,nt(i,j)>>, rt(i,j), diff(kE(i),kbE(i,j))) in
  out(cT, cypher)

system (!_k Reader(k) | !_i !_j Tag(i,j)).

goal wa_Reader1 :
  forall (k:index),
    exec@Reader1(k)
    <=>
    exec@pred(Reader1(k)) && (exists (i,j:index),
      Tag(i,j) < Reader1(k) && Reader(k) < Reader1(k)  &&
      output@Tag(i,j) = input@Reader1(k) &&
      input@Tag(i,j) = output@Reader(k)).
Proof.
  intros.
  expand exec@Reader1(k).
  expand cond@Reader1(k).
  expand output@Reader(k).
  split.

  project; apply tags_neq.

  (* First projection. *)
  intctxt M0.
  exists i, j1.
  depends Reader(k), Reader1(k).

  (* Second projection. *)
  intctxt M0.
  exists i,j.
  depends Reader(k), Reader1(k).

  (* Direction <= *)
  exists i,j.
  apply fail_not_pair to tagT, <input@Tag(i,j),nt(i,j)>.

Qed.

(* Action A is the empty else branch of the reader. *)
goal wa_A :
  forall (k:index),
    exec@A(k)
    <=>
    exec@pred(A(k)) && not (exists (i,j:index),
      Tag(i,j) < A(k) && Reader(k) < A(k)  &&
      output@Tag(i,j) = input@A(k) &&
      input@Tag(i,j) = output@Reader(k)).
Proof.
  intros.
  expand exec@A(k).
  expand cond@A(k).
  expand output@Reader(k).
  split.

  (* Direction => is the obvious one *)

  notleft H1.
  apply H1 to i,j; case H2.
  apply fail_not_pair to tagT, <input@Tag(i,j), nt(i,j)>.

  (* Direction <= *)

  notleft H1.
  apply tags_neq.
  project.

  intctxt M0.
  apply H1 to i,j1; case H2.
  depends Reader(k),A(k).

  intctxt M0.
  apply H1 to i,j; case H2.
  depends Reader(k),A(k).

Qed.

goal lemma : forall (i,j,i1,j1:index),
  output@Tag(i,j) = output@Tag(i1,j1) => i = i1 && j = j1.
Proof.
  intros.
  project.

  assert dec(output@Tag(i,j),kE(i1)) = <tagT,<input@Tag(i1,j1),nt(i1,j1)>>.
  intctxt M1.
  case H0.
  assert dec(output@Tag(i1,j1),kE(i)) = <tagT,<input@Tag(i,j),nt(i,j)>>.
  intctxt M3.
  case H0.
  apply fail_not_pair to tagT,<input@Tag(i,j),nt(i,j)>.
  apply fail_not_pair to tagT,<input@Tag(i1,j1),nt(i1,j1)>.

  assert dec(output@Tag(i,j),kbE(i1,j1)) = <tagT,<input@Tag(i1,j1),nt(i1,j1)>>.
  intctxt M1.
  case H0.
  assert dec(output@Tag(i1,j1),kbE(i,j)) = <tagT,<input@Tag(i,j),nt(i,j)>>.
  intctxt M3.
  case H0.
  apply fail_not_pair to tagT,<input@Tag(i,j),nt(i,j)>.
  apply fail_not_pair to tagT,<input@Tag(i1,j1),nt(i1,j1)>.

Qed.

equiv unlinkability.
Proof.
  enrich seq(k->nr(k)). enrich seq(i,j->nt(i,j)).

  induction t.

  (* Action 1/4: Reader *)

  expand seq(k->nr(k)),k.
  expandall.
  fa 3.

  (* Action 2/4: Reader1 *)

  expand frame@Reader1(k).
  equivalent
    exec@Reader1(k),
    exec@pred(Reader1(k)) &&
    exists (i,j:index),
      Tag(i,j) < Reader1(k) && Reader(k) < Reader1(k)  &&
      output@Tag(i,j) = input@Reader1(k) &&
      input@Tag(i,j) = output@Reader(k).
  apply wa_Reader1 to k.

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
  exists i,j.
  exists i,j.
  project.

  fa.
  (* find condA => condB *)
  intctxt M2.
  apply tags_neq.
  exists j2.
  (* find condB => condA *)
  apply lemma to i,j,i1,j1.
  apply fail_not_pair to tagT, <input@Tag(i,j),nt(i,j)>.

  fa.
  (* find condA => condB *)
  intctxt M2.
  apply tags_neq.
  (* find condB => condA *)
  apply lemma to i,j,i1,j1.
  apply fail_not_pair to tagT, <input@Tag(i,j),nt(i,j)>.

  fa 3; fadup 3.
  fa 3; fadup 3.
  enckp 3, k_fresh.
  expand seq(k->nr(k)),k.
  expand seq(i,j->nt(i,j)),i,j.
  fa 5.
  fresh 6.
  fresh 5; yesif 5.

  (* Action 3/4: A *)

  expand frame@A(k).

  equivalent
    exec@A(k),
    exec@pred(A(k)) && not (exists (i,j:index),
      Tag(i,j) < A(k) && Reader(k) < A(k)  &&
      output@Tag(i,j) = input@A(k) &&
      input@Tag(i,j) = output@Reader(k)).
  apply wa_A to k.

  fa 2.
  fa 3; fadup 3.
  fa 3; fadup 3.

  (* Action 4/4: Tag *)

  expandall.
  fa 2. fa 3.  fa 3.

  enckp 3, k_fresh.
  expand seq(i,j->nt(i,j)),i,j.
  fa 4.
  fresh 5.
  fresh 4; yesif 4.

Qed.
