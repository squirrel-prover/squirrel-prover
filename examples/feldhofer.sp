(**

# FELDHOFER

[B] Martin Feldhofer, Sandra Dominikus, and Johannes Wolkerstorfer.
Strong authentication for RFID systems using the AES algorithm. In
Marc Joye and Jean-Jacques Quisquater, editors, Cryptographic Hard-
ware and Embedded Systems - CHES 2004: 6th International Workshop
Cambridge, MA, USA, August 11-13, 2004. Proceedings, volume 3156
of Lecture Notes in Computer Science, pages 357–370. Springer, 2004.

```
R --> T : nr
T --> R : enc(<tagT,<nr,nt>>,rt,k)
R --> T : enc(<tagR,<nt,nr>>,rr,k)
```

We replace the AES algorithm of the original protocol by a randomized
symmetric encryption, the closest primitive currently supported in
Squirrel. The encryption is assumed to be authenticated, e.g. using the
encrypt-then-mac paradigm. Specifically, we make use of the crypto
assumptions INT-CTXT and ENC-KP on our symmetric encryption.

We add tags for simplicity, and conjecture that the results hold
for the protocol without tags, though at the cost of a proof by
induction for wa_* lemmas.

This is a "light" model without the last check of T.

## UPDATE FOLLOWING THE HIGHER-ORDER EXTENSION

This development was partially broken when Squirrel has been extended to a
higher-order setting, due to changes in the way cryptographic rules are
applied:
```
A Higher-Order Indistinguishability Logic for Cryptographic Reasoning. LICS 2023
```
The problem comes from the fact that the generalized implementation of the
intctxt tactic lacks precision when checking that randomness usage is correct.
In a nutshell, the tactic does not see that the random `rr(k)` used in the
reader process below is only used for a single value of `i,j`, namely the
value selected by the surrounding try-find construct. The problem can be
fixed by reformulating this file, but we are also considering a change of the
tactic's implementation. In the meantime, the file is left as-is with its
admits.
*)

set timeout=10.
set postQuantumSound=true.

channel cR
channel cT

name kE : index -> message
name kbE : index * index -> message

(** Fresh key used for ENC-KP applications. *)
name k_fresh : message

senc enc,dec

abstract tagR : message
abstract tagT : message

name nr : index  -> message
name nt : index * index -> message

name rt : index * index -> message
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
      try find i j such that
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

include Basic.

axiom tags_neq : tagR <> tagT

axiom fail_not_pair (x,y:message): fail <> <x,y>.

lemma wa_Reader1 (k:index):
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
  split => [_ [i j [H [_ _]]]].

  (* Direction => *)
  + project; use tags_neq as _.

    (* First projection. *)
    - intctxt H. 
      (* (LICS'23 changes) problem with the randomness conditions *) admit. 
      (* case 1: in Reader1 *)
        auto.
      (* case 2: in Tag *)
        intro [j0 [H1 H2]]; simpl.
        by exists i, j0.


    (* Second projection. *)
    - intctxt H.
      (* (LICS'23 changes) problem with the randomness conditions *) admit. 
      auto. intro _; simpl. by exists i, j.

  (* Direction <= *)
  + simpl.
    exists i,j. 
    by use fail_not_pair with tagT, <input@Tag(i,j),nt(i,j)>.
Qed.

(* Action Reader2 is the empty else branch of the reader. *)
lemma wa_Reader2 (k:index):
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
  + intro [_ H0] => /= [i j [H1 [_ _]]]. 
    apply H0; exists i,j => /=. 
    by use fail_not_pair with tagT, <input@Tag(i,j), nt(i,j)>.

  (* Direction <= *)
  + intro [_ H0] => /= [i j [H1 [_ _]]].
    apply H0. 
    use tags_neq.
    project.

    - intctxt H1; simpl.
      (* (LICS'23 changes) problem with randomness condition *) admit.
      auto.
      intro [j0 _]. 
      by exists i, j0.       

    - intctxt H1; simpl.
      (* (LICS'23 changes) problem with randomness condition *) admit.
      auto. 
      by intro ?; exists i, j.
Qed.

(** This lemma about unique outputs will be useful for both sides of our system.
    Unfortunately the proof argument involves intctxt and thus requires a
    projection.
    The two subproofs are almost identical. *)
lemma unique_outputs (i,j,i0,j0:index[const]):
  happens(Tag(i,j),Tag(i0,j0)) =>
     output@Tag(i,j) = output@Tag(i0,j0) => i = i0 && j = j0.
Proof.
  intro H Meq.
  project.

  + assert dec(output@Tag(i,j),kE(i0)) = <tagT,<input@Tag(i0,j0),nt(i0,j0)>> as Meq0;
    1: by expand output, cipher.
    intctxt Meq0; try auto; clear Meq0.
    - by use fail_not_pair with tagT,<input@Tag(i0,j0),nt(i0,j0)>.
    - (* (LICS'23 changes) problem w/ randomness condition *) admit.
    - intro [j1 [? ?]]. 
      assert dec(output@Tag(i0,j0),kE(i)) = <tagT,<input@Tag(i,j),nt(i,j)>> as Meq2;
      1: by expand output, cipher.
      intctxt Meq2; clear Meq2; try auto.
      * by use fail_not_pair with tagT,<input@Tag(i,j),nt(i,j)>.
      * intro [i1 k ?] /=. 
        have A : j1 = j0 by auto.
        rewrite A in *; clear A. 
        rewrite -Meq in *. 
        admit. (* (LICS'23 changes) pb w/ randomness condition *) 

  + assert dec(output@Tag(i,j),kbE(i0,j0)) = <tagT,<input@Tag(i0,j0),nt(i0,j0)>>
    as Meq0;
    1: by expand output, cipher.
    intctxt Meq0; try auto. 
    - by use fail_not_pair with tagT,<input@Tag(i0,j0),nt(i0,j0)>.
    - (* (LICS'23 changes) pb w/ randomness condition *) admit.
    - assert dec(output@Tag(i0,j0),kbE(i,j)) = <tagT,<input@Tag(i,j),nt(i,j)>> as Meq2;
      1: by expand output, cipher.
      intctxt Meq2; try auto.
       * by use fail_not_pair with tagT,<input@Tag(i,j),nt(i,j)>.
       * (* (LICS'23 changes) pb w/ randomness condition *) admit.
Qed.

equiv unlinkability.
Proof.
  enrich seq(k:index => nr(k)), seq(i,j:index => nt(i,j)).

  induction t.

  (* init *)
  + auto.

  (* Action 1/4: Reader *)
  + by expandall; apply IH.

  (* Action 2/4: Reader1 *)
  + expand frame.
    rewrite wa_Reader1; 1:auto. 

    expand output@Reader1(k).
    fa 2; fa 3. 
    deduce 3.

    have ->:
      (if
         exec@pred(Reader1(k)) &&
         (exists (i,j:index),
           Tag(i,j) < Reader1(k) &&
           Reader(k) < Reader1(k) &&
           output@Tag(i,j) = input@Reader1(k) &&
           input@Tag(i,j) = output@Reader(k))
       then
         (try find i j such that
            dec(input@Reader1(k),diff(kE(i),kbE(i,j))) <> fail &&
            fst(dec(input@Reader1(k),diff(kE(i),kbE(i,j)))) = tagT &&
            fst(snd(dec(input@Reader1(k),diff(kE(i),kbE(i,j))))) = nr(k)
          in
            enc(<tagR,<snd(snd(dec(input@Reader1(k),diff(kE(i),kbE(i,j))))),
                       nr(k)>>,
                rr(k),
                diff(kE(i),kbE(i,j)))))
      =
      (if
         exec@pred(Reader1(k)) &&
         (exists (i,j:index),
           Tag(i,j) < Reader1(k) &&
           Reader(k) < Reader1(k) &&
           output@Tag(i,j) = input@Reader1(k) &&
           input@Tag(i,j) = output@Reader(k))
       then
         (try find i j such that
            exec@pred(Reader1(k)) &&
            (Tag(i,j) < Reader1(k) &&
             Reader(k) < Reader1(k) &&
             output@Tag(i,j) = input@Reader1(k) &&
             input@Tag(i,j) = output@Reader(k))
          in
            enc(<tagR,<nt(i,j),nr(k)>>,rr(k),
                diff(kE(i),kbE(i,j))))). 
    {
      fa; try (intro *; auto).
      intro [_ [i j _]] /=.
      project.

      * fa => //.
        (* find condA => condB *)
        - intro [Mneq _ _].
          intctxt Mneq; simpl.
          (* (LICS'23 changes) pb w/ randomness condition *) admit. 
           by use tags_neq.
          intro [j1 _]; by exists j1.

        (* find condB => condA *)
        - intro _. 
          have A := localize(unique_outputs i j i0 j0). 
          (have [A1 A2] := A _ _; 1,2: auto); clear A.
          use fail_not_pair with tagT, <input@Tag(i,j),nt(i,j)>. 
          auto.

      * fa => //.
        (* find condA => condB *)
        - intro [Mneq _ _].
          intctxt Mneq; simpl.
          (* (LICS'23 changes) pb w/ randomness condition *) admit. 
          by use tags_neq.
          auto.

        (* find condB => condA *)
        - intro _.
          have A := localize(unique_outputs i j i0 j0). 
          (have [A1 A2] := A _ _; 1,2: auto); clear A.
          use fail_not_pair with tagT, <input@Tag(i,j),nt(i,j)>.
          auto.
    }.

    fa 3; deduce 3.
    fa 3; deduce 3.
    enckp 3, k_fresh; 1: auto.
    fa 3. 
    fresh 4; 1: auto. 
    fresh 4; 1:auto.
    apply IH.

  (* Action 3/4: Reader2 *)

  + expand frame.
    rewrite wa_Reader2; 1:auto.

    fa 2.
    fa 3; deduce 3.
    by fa 3; deduce 3.

  (* Action 4/4: Tag *)

  + expandall.
    fa 2. fa 3. fa 3.

    enckp 3, k_fresh; 1: auto.

    fa 3.
    fresh 5; 1:auto.
    fresh 4; 1: auto.
    apply IH.
Qed.
