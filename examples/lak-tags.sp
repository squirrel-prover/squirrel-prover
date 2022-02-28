(*******************************************************************************
LAK WITH PAIRS AND TAGS

[D] Lucca Hirschi, David Baelde, and Stéphanie Delaune. A method for
unbounded verification of privacy-type properties. Journal of Computer
Security, 27(3):277–342, 2019.

R --> T : nR
T --> R : <nT,h(<<nR,nT>,tag1>,kT)>
R --> T : h(<<h(<<nR,nT>,tag1>,kT),nR>,tag2>,kR)

We consider tags in the messages (tag1 and tag2) to ease the proof.

This is a "light" model without the last check of T.
*******************************************************************************)

set postQuantumSound=true.

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

include Basic.

axiom tags_neq : tag1 <> tag2.

goal wa_R1_R2 (tau:timestamp,j:index):
  happens(tau) =>
  (exists (i,k:index)
     snd(input@tau) = h(<<nR(j),fst(input@tau)>,tag1>,diff(key(i),key'(i,k))))
  =
  (exists (i,k:index),
     T(i,k) < tau && R(j) < T(i,k) &&
     snd(output@T(i,k)) = snd(input@tau) &&
     fst(output@T(i,k)) = fst(input@tau) &&
     input@T(i,k) = output@R(j)).
Proof.
  intro Hap.
  rewrite eq_iff; split.

  (* COND => WA *)
  + intro [i k H].
    use tags_neq; project.

    (* LEFT *)
    - euf H => _ _ _ //.
      exists i,k0.
      assert input@T(i,k0)=nR(j) as Meq1; 1: auto.
      fresh Meq1 => C /=.
      case C => //.
      * by depends R(j),R1(j).
      * by depends R(j),R2(j).

    (* RIGHT *)
    - euf H => _ _ _ //.
      exists i,k.
      assert input@T(i,k)=nR(j) as Meq1; 1: by auto.
      fresh Meq1 => C /=.
      case C => //.
      * by depends R(j),R1(j).
      * by depends R(j),R2(j).

  (* WA => COND *)
  + intro [i k _]; exists i,k.
    by expand output, m2.
Qed.

(** The next two lemmas are more precise variants of the previous one,
    specifically for R1. They are useful to simplify the try-find construct
    in the output of that action. Note that the proofs of the next two
    lemmas are almost identical, but their statements differ in the treatment
    of index k, and they deal with distinct systems. *)

goal [left] wa_R1_left (i,j:index):
  happens(R1(j)) =>
  (snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key(i)))
  =
  (exists k:index,
     T(i,k) < R1(j) && R(j) < T(i,k) &&
     snd(output@T(i,k)) = snd(input@R1(j)) &&
     fst(output@T(i,k)) = fst(input@R1(j)) &&
     input@T(i,k) = output@R(j)).
Proof.
  intro Hap.
  rewrite eq_iff; split; 2: by intro [k _]; expand output, m2.

  intro Meq.
  use tags_neq.
  euf Meq => _ _ _ //.
  exists k.
  assert input@T(i,k) = nR(j) as Meq1; 1: auto.
  fresh Meq1 => C /=.
  case C => //.
  by depends R(j),R2(j).
Qed.

goal [right] wa_R1_right (i,j,k:index):
  happens(R1(j)) =>
  (snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k)))
  =
  (T(i,k) < R1(j) && R(j) < T(i,k) &&
   snd(output@T(i,k)) = snd(input@R1(j)) &&
   fst(output@T(i,k)) = fst(input@R1(j)) &&
   input@T(i,k) = output@R(j)).
Proof.
  intro Hap.
  rewrite eq_iff; split; 2: by intro [k _]; expand output, m2.

  intro Meq.
  use tags_neq.
  euf Meq => _ _ _ //.
  assert input@T(i,k) = nR(j) as Meq1; 1: auto.
  fresh Meq1 => C /=.
  case C => //.
  by depends R(j),R2(j).
Qed.

(** Equality used to rewrite the try-find in R1
    so that its condition can be discharged using fadup. *)
goal wa_R1_tryfind (j:index) : happens(R1(j)) =>
  (if exec@pred(R1(j)) && cond@R1(j) then
   try find i,k such that
     snd(input@R1(j)) =
     h(<<nR(j),fst(input@R1(j))>,tag1>,diff(key(i),key'(i,k)))
   in h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k))))
  =
  (if exec@pred(R1(j)) && cond@R1(j) then
   try find i,k such that
     exec@pred(R1(j)) &&
     (T(i,k) < R1(j) && R(j) < T(i,k) &&
      snd(output@T(i,k)) = snd(input@R1(j)) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      input@T(i,k) = output@R(j))
   in
   h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k)))).
Proof.
  intro Hap.
  case exec@pred(R1(j)) => Hexec; 2: auto.
  case cond@R1(j) => Hcond; 2: auto.
  simpl.

  expand cond; rewrite wa_R1_R2 in Hcond => //.
  destruct Hcond as [i0 k0 Hcond].

  (* It is important to project before using "fa" on
     the "try find" construct so that the redundant
     index k on the left is treated smartly. *)
  project.

  + fa; try auto.
    intro Heq.
    rewrite wa_R1_left in Heq; 1: auto.
    destruct Heq as [k1 Heq].
    assert nT(i0,k0) = nT(i,k1); 1: auto.
    eqnames.
    by exists k0.

  + fa; try auto.
    intro Heq.
    by rewrite wa_R1_right in Heq.

Qed.

equiv unlinkability.
Proof.
  induction t.

  (* Case init *)
  + auto.

  (* Case R *)
  + expand frame, exec, cond, output.
    fa 0; fa 1; fa 1.
    fresh 1; rewrite if_true. {
      repeat split => // j0 H1.
      by depends R(j0),R2(j0).
      by depends R(j0),R1(j0).
    }
    auto.

  (* Case R1 *)
  + expand frame, exec, output.
    fa 0; fa 1.
    rewrite wa_R1_tryfind; 1: auto.
    expand cond; rewrite wa_R1_R2 => //.
    fa 2; fadup 1.
    fa 1; fadup 1.
    prf 1.
    rewrite if_true.
    by use tags_neq; project.
    by fresh 1.

  (* Case R2 *)
  + expand frame, exec, output.
    fa 0; fa 1.
    expand cond; rewrite wa_R1_R2; 1: auto.
    by fadup 1.

  (* Case T *)
  + expand frame, exec, cond, output.
    expand m2(i,k)@T(i,k).
    fa 0. fa 1. fa 1. fa 1.
    prf 2.
    rewrite if_true. {
      simpl.
      use tags_neq.
      by project; repeat split; intro > _ _ [[_ Meq] _]; fresh Meq.
    }
    fresh 2.
    by fresh 1; rewrite if_true.
Qed.
