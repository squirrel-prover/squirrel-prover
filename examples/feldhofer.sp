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

set timeout=4.

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

goal wa_Reader1 (k:index):
  happens(Reader1(k)) => 
    (exec@Reader1(k)
     <=>
     exec@pred(Reader1(k)) && (exists (i,j:index),
       Tag(i,j) < Reader1(k) && Reader(k) < Reader1(k)  &&
       output@Tag(i,j) = input@Reader1(k) &&
       input@Tag(i,j) = output@Reader(k))).
Proof.
  intro *.
  depends Reader(k), Reader1(k).
  expand exec, cond, output.
  split.

  project; use tags_neq.

  (* First projection. *)
  intctxt Mneq.
  by exists i, j0.

  (* Second projection. *)
  intctxt Mneq.
  by exists i,j. 

  (* Direction <= *)
  exists i,j.
  expand output.
  by use fail_not_pair with tagT, <input@Tag(i,j),nt(i,j)>. 
Qed.

(* Action Reader2 is the empty else branch of the reader. *)
goal wa_Reader2 (k:index):
  happens(Reader2(k)) =>
    (exec@Reader2(k)
     <=>
     exec@pred(Reader2(k)) && not (exists (i,j:index),
       Tag(i,j) < Reader2(k) && Reader(k) < Reader2(k)  &&
       output@Tag(i,j) = input@Reader2(k) &&
       input@Tag(i,j) = output@Reader(k))).
Proof.
  intro *.
  expand exec, cond.
  depends Reader(k),Reader2(k).
  expand output.
  split.

  (* Direction => is the obvious one *)
  expand output. 
  notleft H0.
  use H0 with i,j; case H1.
  by use fail_not_pair with tagT, <input@Tag(i,j), nt(i,j)>.

  (* Direction <= *)

  notleft H0.
  use tags_neq.
  project.

  intctxt Mneq.
  by use H0 with i,j0; case H1.

  intctxt Mneq.
  by use H0 with i,j; case H1.
Qed.

goal lemma (i,j,i1,j1:index):
  happens(Tag(i,j),Tag(i1,j1)) => 
     output@Tag(i,j) = output@Tag(i1,j1) => i = i1 && j = j1.
Proof.
  intro *.
  project. 

  assert dec(output@Tag(i,j),kE(i0)) = <tagT,<input@Tag(i0,j0),nt(i0,j0)>>.
  intctxt Meq0.
  case H.
  assert dec(output@Tag(i0,j0),kE(i)) = <tagT,<input@Tag(i,j),nt(i,j)>>.
  intctxt Meq2.
  by case H.
  by use fail_not_pair with tagT,<input@Tag(i,j),nt(i,j)>.
  by use fail_not_pair with tagT,<input@Tag(i0,j0),nt(i0,j0)>.

  assert dec(output@Tag(i,j),kbE(i0,j0)) = <tagT,<input@Tag(i0,j0),nt(i0,j0)>>.
  intctxt Meq0.
  case H.
  assert dec(output@Tag(i0,j0),kbE(i,j)) = <tagT,<input@Tag(i,j),nt(i,j)>>.
  intctxt Meq2.
  by case H.
  by use fail_not_pair with tagT,<input@Tag(i,j),nt(i,j)>.
  by use fail_not_pair with tagT,<input@Tag(i0,j0),nt(i0,j0)>.
Qed.

equiv unlinkability.
Proof.
  enrich seq(k->nr(k)), seq(i,j->nt(i,j)).

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
  by use wa_Reader1 with k.

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
  by use tags_neq.
  by exists j1.

  (* find condB => condA *)
  use lemma with i,j,i0,j0.
  by use fail_not_pair with tagT, <input@Tag(i,j),nt(i,j)>. 

  fa. 
  (* find condA => condB *)
  intctxt Mneq. 
  by use tags_neq.
  (* find condB => condA *)
  use lemma with i,j,i0,j0 as Hlem. 
  by use fail_not_pair with tagT, <input@Tag(i,j),nt(i,j)>.

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
  by use wa_Reader2 with k.

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
