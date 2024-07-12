(*******************************************************************************
LAK WITH PAIRS AND TAGS

[D] Lucca Hirschi, David Baelde, and Stéphanie Delaune. A method for
unbounded verification of privacy-type properties. Journal of Computer
Security, 27(3):277–342, 2019.

R --> T : nR
T --> R : <nT,h(<<nR,nT>,tag1>,k)>
R --> T : h(<<h(<<nR,nT>,tag1>,k),nR>,tag2>,k)

We consider tags in the messages (tag1 and tag2) to ease the proof.

This is a "light" model without the last check of T.
*******************************************************************************)

set postQuantumSound=true.

hash h

abstract ok : message
abstract ko : message

abstract tag1 : message
abstract tag2 : message

name key : index -> message
name key': index * index -> message

channel cT.
channel cR.

process tag(i,j:index) =
  new nT;
  in(cR,nR);
  let m2 = h(<<nR,nT>,tag1>,diff(key(i),key'(i,j))) in
  out(cT,<nT,m2>).

process reader =
  new nR;
  out(cR,nR);
  in(cT,x);
  if exists (i,k:index),
     snd(x) = h(<<nR,fst(x)>,tag1>,diff(key(i),key'(i,k)))
  then
    out(cR, try find i k such that
              snd(x) = h(<<nR,fst(x)>,tag1>,diff(key(i),key'(i,k)))
            in
              h(<<snd(x),nR>,tag2>,diff(key(i),key'(i,k))))
  else
    out(cR,ko).

system ((!_k R: reader) | (!_i !_j T: tag(i,j))).

include Basic.

axiom tags_neq : tag1 <> tag2.

lemma wa_R1_R2 (tau:timestamp,k:index):
  happens(tau) =>
  (exists (i,j:index),
     snd(input@tau) = h(<<nR(k),fst(input@tau)>,tag1>,diff(key(i),key'(i,j))))
  =
  (exists (i,j:index),
     T(i,j) < tau && R(k) < T(i,j) &&
     snd(output@T(i,j)) = snd(input@tau) &&
     fst(output@T(i,j)) = fst(input@tau) &&
     input@T(i,j) = output@R(k)).
Proof.
  intro Hap.
  rewrite eq_iff; split.

  (* COND => WA *)
  + intro [i j H].
    use tags_neq; project.

    (* LEFT *)
    - euf H => [j0 [_ _]] //.
      exists i,j0.
      assert input@T(i,j0)=nR(k) as Meq1 by auto.
      fresh Meq1 => C /=;
      [1: auto
      |2: by depends R(k),R1(k)
      |3: by depends R(k),R2(k)].

    (* RIGHT *)
    - euf H => [l [_ _]] //.
      exists i,j.
      assert input@T(i,j)=nR(k) as Meq1 by auto.
      fresh Meq1 => C /=;
      [1: auto
      |2: by depends R(k),R1(k)
      |3: by depends R(k),R2(k)].

  (* WA => COND *)
  + intro [i j _]; exists i,j.
    by expand output, m2.
Qed.

(** The next two lemmas are more precise variants of the previous one,
    specifically for R1. They are useful to simplify the try-find construct
    in the output of that action. Note that the proofs of the next two
    lemmas are almost identical, but their statements differ in the treatment
    of index k, and they deal with distinct systems. *)

lemma [default/left] wa_R1_left (i,k:index):
  happens(R1(k)) =>
  (snd(input@R1(k)) = h(<<nR(k),fst(input@R1(k))>,tag1>,key(i)))
  =
  (exists j,
     T(i,j) < R1(k) && R(k) < T(i,j) &&
     snd(output@T(i,j)) = snd(input@R1(k)) &&
     fst(output@T(i,j)) = fst(input@R1(k)) &&
     input@T(i,j) = output@R(k)).
Proof.
  intro Hap.
  rewrite eq_iff; split; 2: by intro [j _]; expand output, m2.

  intro Meq.
  use tags_neq.
  euf Meq => [j [_ _]] //.
  exists j.
  assert input@T(i,j) = nR(k) as Meq1 by auto.
  fresh Meq1 => C /=;
   [1: auto
   |2: by depends R(k),R1(k)
   |3: by depends R(k),R2(k)].
Qed.

lemma [default/right] wa_R1_right (i,j,k:index):
  happens(R1(k)) =>
  (snd(input@R1(k)) = h(<<nR(k),fst(input@R1(k))>,tag1>,key'(i,j)))
  =
  (T(i,j) < R1(k) && R(k) < T(i,j) &&
   snd(output@T(i,j)) = snd(input@R1(k)) &&
   fst(output@T(i,j)) = fst(input@R1(k)) &&
   input@T(i,j) = output@R(k)).
Proof.
  intro Hap.
  rewrite eq_iff; split; 2: by intro [j _]; expand output, m2.

  intro Meq.
  use tags_neq.
  euf Meq => [l [_ _]] //.
  assert input@T(i,j) = nR(k) as Meq1 by auto.
  fresh Meq1 => C /=;
   [1: auto
   |2: by depends R(k),R1(k)
   |3: by depends R(k),R2(k)].
Qed.

(** Equality used to rewrite the try-find in R1
    so that its condition can be discharged using deduce. *)
lemma wa_R1_tryfind (k:index) : happens(R1(k)) =>
  (if exec@pred(R1(k)) && cond@R1(k) then
   try find i j such that
     snd(input@R1(k)) =
     h(<<nR(k),fst(input@R1(k))>,tag1>,diff(key(i),key'(i,j)))
   in h(<<snd(input@R1(k)),nR(k)>,tag2>,diff(key(i),key'(i,j))))
  =
  (if exec@pred(R1(k)) && cond@R1(k) then
   try find i j such that
     exec@pred(R1(k)) &&
     (T(i,j) < R1(k) && R(k) < T(i,j) &&
      snd(output@T(i,j)) = snd(input@R1(k)) &&
      fst(output@T(i,j)) = fst(input@R1(k)) &&
      input@T(i,j) = output@R(k))
   in
   h(<<snd(input@R1(k)),nR(k)>,tag2>,diff(key(i),key'(i,j)))).
Proof.
  intro Hap.
  case exec@pred(R1(k)) => Hexec; 2: auto.
  case cond@R1(k) => Hcond; 2: auto.
  simpl.
  (* It is important to project before using "fa" on
     the "try find" construct so that the redundant
     index k on the left is treated smartly. *)
  project.
  + fa => // Heq.
    by rewrite wa_R1_left in Heq.
  + fa => // Heq.
    by rewrite wa_R1_right in Heq.
Qed.

equiv unlinkability.
Proof.
  induction t.

  (* Case init *)
  + auto.

  (* Case R *)
  + expand frame, exec, cond, output.
    fa !<_,_>, if _ then _.
    fresh 1. {
      repeat split => * //;
      [1: by depends R(k),R1(k)
      |2: by depends R(k),R2(k)]. 
    }
    auto.

  (* Case R1 *)
  + expand frame, exec, output.
    fa !<_,_>.
    rewrite wa_R1_tryfind; 1: auto. 
    expand cond; rewrite wa_R1_R2; 1: auto. 
    fa 2; deduce 1.
    fa 1; deduce 1.
    prf 1.
    * by use tags_neq. 
    * by use tags_neq. 
    * by fresh 1.

  (* Case R2 *)
  + expand frame, exec, output.
    fa !<_,_>.
    expand cond; rewrite wa_R1_R2; 1: auto. 
    by deduce 1.

  (* Case T *)
  + expand frame, exec, cond, output.
    expand m2 i j@T(i,j).
    fa !<_,_>, if _ then _, <_,_>.
    prf 2.
    * use tags_neq.
      repeat split => //; by intro > _ _ [[_ Meq] _]; fresh Meq.
    * use tags_neq.
      repeat split => //; by intro > _ _ [[_ Meq] _]; fresh Meq.
    * fresh 2; 1:auto.
      by fresh 1.
Qed.
