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
set autoIntro=false.
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

axiom fail_not_pair (x,y:message): fail <> <x,y>.

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
  depends Reader(k), Reader1(k); 1: auto.
  intro C.
  expand exec, cond.
  split => [_ [i j [[H _] _]]].

  project; use tags_neq as _.

  (* First projection. *)
  intctxt H => // _ _ _ /=.
  by exists i, j0.

  (* Second projection. *)
  intctxt H => // _ _ _ /=.
  by exists i, j.

  (* Direction <= *)
  simpl.
  exists i,j.
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
  depends Reader(k),Reader2(k); 1: auto.
  intro C.
  split.

  (* Direction => is the obvious one *)
  intro [_ H0] => /= [i j [[H1 _] _]].
  notleft H0.
  use H0 with i,j; case H1.
  clear H0.
  expand output, cipher.
  use fail_not_pair with tagT, <input@Tag(i,j), nt(i,j)>.
  by case H.

  (* Direction <= *)
  intro [_ H0] => /= [i j [[H1 _] _]].
  notleft H0.
  use tags_neq.
  project.

  intctxt H1 => // _ _ _.
  use H0 with i,j0 as C1.
  clear H0.
  by expand output, cipher; case C1.

  intctxt H1 => // _ _ _.
  use H0 with i,j as C1.
  clear H0.
  by expand output, cipher; case C1.
Qed.

(** This lemma about unique outputs will be useful for both sides of our system.
  * Unfortunately the proof argument involves intctxt and thus requires a projection.
  * The two subproofs are almost identical. *)
goal unique_outputs (i,j,i0,j0:index):
  happens(Tag(i,j),Tag(i0,j0)) =>
     output@Tag(i,j) = output@Tag(i0,j0) => i = i0 && j = j0.
Proof.
  intro H Meq.
  project.

  assert dec(output@Tag(i,j),kE(i0)) = <tagT,<input@Tag(i0,j0),nt(i0,j0)>> as Meq0;
  1: by expand output, cipher.
  intctxt Meq0 => C //.
  case C => //.
  assert dec(output@Tag(i0,j0),kE(i)) = <tagT,<input@Tag(i,j),nt(i,j)>> as Meq2;
  1: by expand output, cipher.
  intctxt Meq2 => C1 //.
  by case C1.
  by use fail_not_pair with tagT,<input@Tag(i,j),nt(i,j)>.
  by use fail_not_pair with tagT,<input@Tag(i0,j0),nt(i0,j0)>.

  assert dec(output@Tag(i,j),kbE(i0,j0)) = <tagT,<input@Tag(i0,j0),nt(i0,j0)>>
  as Meq0;
  1: by expand output, cipher.
  intctxt Meq0 => C //.
  case C => //.
  assert dec(output@Tag(i0,j0),kbE(i,j)) = <tagT,<input@Tag(i,j),nt(i,j)>> as Meq2;
  1: by expand output, cipher.
  intctxt Meq2 => C1 //.
  by case C1.
  by use fail_not_pair with tagT,<input@Tag(i,j),nt(i,j)>.
  by use fail_not_pair with tagT,<input@Tag(i0,j0),nt(i0,j0)>.
Qed.

equiv unlinkability.
Proof.
  enrich seq(k:index -> nr(k)), seq(i,j:index -> nt(i,j)).

  induction t.

  (* init *)
  auto.

  (* Action 1/4: Reader *)

  by expandall; apply IH.

  (* Action 2/4: Reader1 *)

  expand frame.
  equivalent
    exec@Reader1(k),
    exec@pred(Reader1(k)) &&
    exists (i,j:index),
      Tag(i,j) < Reader1(k) && Reader(k) < Reader1(k)  &&
      output@Tag(i,j) = input@Reader1(k) &&
      input@Tag(i,j) = output@Reader(k);
  1: by use wa_Reader1 with k.

  expand output.
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
  intro *; auto.
  by intro [_ [i j _]] /=; exists i,j.
  intro [_ [i j _]] /=.
  project.

  fa => //.
  (* find condA => condB *)
  intro [Mneq _ _].
  intctxt Mneq => // _ _ _;
  [1: by use tags_neq|
   2: by exists j1].

  (* find condB => condA *)
  intro _.
  use unique_outputs with i,j,i0,j0 as [_ _]; 2,3: auto.
  use fail_not_pair with tagT, <input@Tag(i,j),nt(i,j)>.
  by expand output, cipher.

  fa => //.
  (* find condA => condB *)
  intro [Mneq _ _].
  intctxt Mneq => // _ _ [_ _].
  by use tags_neq.

  (* find condB => condA *)
  intro _.
  use unique_outputs with i,j,i0,j0 as [_ _]; 2,3: auto.
  use fail_not_pair with tagT, <input@Tag(i,j),nt(i,j)>.
  by expand output, cipher.

  auto.

  fa 3; fadup 3.
  fa 3; fadup 3.
  enckp 3, k_fresh; 1: auto.
  fa 3. fresh 4; yesif 4; 1: auto. fresh 4.
  apply IH.

  (* Action 3/4: Reader2 *)

  expand frame.

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
  fa 2. fa 3. fa 3.

  enckp 3, k_fresh; 1: auto.

  fa 3.
  fresh 5.
  fresh 4; yesif 4; 1: auto.
  apply IH.
Qed.
