include Libs.
include Games.

(****************************************************************************
# Protocol steps definition
*****************************************************************************)

channel c.

(* ------------------------------------------------------------------- *)
(* Randomness *)

(* signature keys for Alice and Bob *)
name skA : sk_sign.
name skB : sk_sign.
(* commitement keys for Alice and Bob *)
name kc0 : k_comm.
name kc1 : k_comm.
(* token for blinding for Alice and Bob *)
name tkA : token_bsign.
name tkB : token_bsign.
(* encryptions randomness for Alice and Bob*)
name seedA_enc1 : seed.
name seedB_enc1 : seed.
name seedA_enc2 : seed.
name seedB_enc2 : seed.
name seedA_sign : seed.
name seedB_sign : seed.
(* mixnet encryption key *)
name sk_mix1 : sk_enc.
name sk_mix2 : sk_enc.


action V_1 : 0.
action V_2 : 0.
action Avote : 0.
action Bvote : 0.
action Aopening : 0.
action Bopening : 0.
action MVC : 1.
action MOC : 1.

(* Dummy messages *)
abstract zero_enc1 : message.
abstract zero_enc2 : message.

(* ------------------------------------------------------------------
## Ballot box
------------------------------------------------------------------- *)

mutable BB : (index -> (message*signed)) = witness.
abstract setBB: message.

mutex mutex_BB:0.

process set_BB =
  in(c,x);
  let bb = read x in
  lock mutex_BB;
  BB := bb;
  unlock mutex_BB.

(* ------------------------------------------------------------------
## Common mix-net behaviour
------------------------------------------------------------------- *)

mutable box (i:index) : message = zero.

mutex mutex_box:0.

process mixer_vote_publish =
  lock mutex_box;
  let Box = fun i => box i in
  unlock mutex_box;
  let commits = shuffle Box in
  out(c, if partial_injective Box (fun i => MVC i) then commits).

mutable count (i: index) : message = zero.

mutex mutex_count:0.

process mixer_open_publish_CCA
  (pkAdmin : pk_sign)
  (cmA,cmB : message)
=
  let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
  let ubB = unblind cmB pkAdmin tkB (read (input@Bvote)) in
  let acc_A = baccepte cmA pkAdmin tkA (read (input@Avote)) in
  let acc_B = baccepte cmB pkAdmin tkB (read (input@Bvote)) in
  lock mutex_BB;
  lock mutex_box;
  lock mutex_count;
  let votedA = mem_bb (cmA,ubA) BB in
  let votedB = mem_bb (cmB,ubB) BB in
  let Count = fun i => count i in
  let Box   = fun i => box   i in
  unlock mutex_BB;
  unlock mutex_box;
  unlock mutex_count;
  let commAB =
      (exists i, happens(MVC(i)) && Avote < MVC(i) && (input@MVC(i)) =
        format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1))
   && (exists i, happens(MVC(i)) && Bvote < MVC(i) && (input@MVC(i)) =
       format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1))
   && acc_A && acc_B
  in
  let voteAB =
      (exists i, happens(MOC(i)) && (input@MOC(i)) =
        format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2))
   && (exists i, happens(MOC(i)) && (input@MOC(i)) =
       format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2))
   && votedA && votedB
  in
  let votes = shuffle Count in
  out(c, if commAB && voteAB then if partial_injective Count (fun i => MOC i) then votes).

process mixer_open_publish
  (pkAdmin : pk_sign)
  (cmA,cmB : message)
  (kcA,kcB : k_comm)
=
  let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
  let ubB = unblind cmB pkAdmin tkB (read (input@Bvote)) in
  let acc_A = baccepte cmA pkAdmin tkA (read (input@Avote)) in
  let acc_B = baccepte cmB pkAdmin tkB (read (input@Bvote)) in
  let mA = <cmA, format ubA> in
  let mB = <cmB, format ubB> in
  lock mutex_BB;
  lock mutex_count;
  lock mutex_box;
  let iA = find_bb (cmA,ubA) BB in
  let iB = find_bb (cmB,ubB) BB in
  let votedA = mem_bb (cmA,ubA) BB in
  let votedB = mem_bb (cmB,ubB) BB in
  let ma' = <format iA, format kcA> in
  let mb' = <format iB, format kcB> in
  let Count = fun i => count i in
  let Box   = fun i => box   i in
  unlock mutex_BB;
  unlock mutex_count;
  unlock mutex_box;
  let commAB =
      (exists i, happens(MVC(i)) &&  Avote < MVC(i) && (input@MVC(i)) =
        format (encr mA (pk_enc sk_mix1) seedA_enc1))
   && (exists i, happens(MVC(i)) &&  Bvote < MVC(i) && (input@MVC(i)) =
       format (encr mB (pk_enc sk_mix1) seedB_enc1))
   && acc_A && acc_B
  in
  let voteAB =
      (exists i, happens(MOC(i)) && (input@MOC(i)) =
        format (encr ma'  (pk_enc sk_mix2) seedA_enc2))
   && (exists i, happens(MOC(i)) && (input@MOC(i)) =
       format (encr mb' (pk_enc sk_mix2) seedB_enc2))
   && votedA && votedB
  in
  let votes = shuffle Count in
  out(c, if commAB && voteAB then
         if partial_injective Count (fun i => MOC i) then votes).


(* ------------------------------------------------------------------
## Voters: real and CCA2-rewritten
------------------------------------------------------------------- *)

process Voter_CCA
  (cm : message) (pkAdmin : pk_sign)
  (tk : token_bsign)
  (seed_enc0, seed_enc1 : seed)
=
  let b  = blind cm pkAdmin tk in
  $auth : out(c,format b);

  in(c,sb);
  let sb     = read sb in
  let acc    = baccepte cm pkAdmin tk sb in
  let ublnd  = unblind  cm pkAdmin tk sb in
  $vote : out (c,
    if acc then format (encr zero_enc1 (pk_enc sk_mix1) seed_enc0));

  in (c,setBB);
  lock mutex_BB;
  let voted = mem_bb (cm,ublnd) BB in
  let i = find_bb (cm,ublnd) BB in
  unlock mutex_BB;
  $opening : out(c,
    if acc && voted then format (encr zero_enc2 (pk_enc sk_mix2) seed_enc1)).


process Alice_CCA (v:message) (kcA : k_comm) (pkAdmin : pk_sign) =
  Voter_CCA(v, pkAdmin, tkA, seedA_enc1, seedA_enc2).

process Bob_CCA (v:message) (kcB : k_comm) (pkAdmin : pk_sign) =
  Voter_CCA(v, pkAdmin, tkB, seedB_enc1, seedB_enc2).


process Voter_real
  (cm : message) (pkAdmin : pk_sign)
  (sk : sk_sign) (kc : k_comm) (tk : token_bsign)
  (seed_enc0, seed_enc1, seed_sign : seed)
=
  let b  = blind cm pkAdmin tk in
  $auth : out(c,format b);

  in(c,sb);
  let sb     = read sb in
  let acc    = baccepte cm pkAdmin tk sb in
  let ublnd  = unblind  cm pkAdmin tk sb in
  $vote : out (c, if acc then
    format (encr ((<cm,format ublnd>))
            (pk_enc sk_mix1) seed_enc0));

  in (c,setBB);
  lock mutex_BB;
  let voted = mem_bb (cm,ublnd) BB in
  let i = find_bb (cm,ublnd) BB in
  unlock mutex_BB;
  $opening : out(c, if acc && voted then
  format (encr (<format i,format kc>)
         (pk_enc sk_mix2) seed_enc1)).


process Alice_real (v:message) (kcA : k_comm) (pkAdmin : pk_sign) =
  Voter_real(v, pkAdmin, skA, kcA, tkA, seedA_enc1, seedA_enc2, seedA_sign).

process Bob_real (v:message) (kcB : k_comm) (pkAdmin : pk_sign) =
  Voter_real(v, pkAdmin, skB, kcB, tkB, seedB_enc1, seedB_enc2, seedB_sign).


(* ------------------------------------------------------------------
## Mix net real and CCA2 rewritten
------------------------------------------------------------------- *)

process mixer_vote_collect_real
  (cmA : message) (cmB : message)
  (pkAdmin : pk_sign)
=
  !_i (
    in(c,m);
    let m   = read m in
    let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
    let ubB =  unblind cmB pkAdmin tkB (read (input@Bvote))  in
    lock mutex_box;
    box(i):=
      if Avote < MVC(i) &&
         m = encr ((<cmA,format ubA>)) (pk_enc sk_mix1) seedA_enc1
      then ( <cmA,format ubA>)
      else if Bvote < MVC(i) &&
              m = encr ((<cmB,format ubB>)) (pk_enc sk_mix1) seedB_enc1
      then (<cmB,format ubB>)
      else  decr m sk_mix1;
    unlock mutex_box
  ).


process mixer_open_collect_real (cmA,cmB : message)
  (kcA,kcB : k_comm)
  (pkAdmin : pk_sign)
=
  !_j(
    in(c,m);
    let m  = read m in
    let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
    let ubB = unblind cmB pkAdmin tkB (read (input@Bvote)) in
    lock mutex_BB;
    lock mutex_count;
    let iA = find_bb (cmA,ubA) BB in
    let iB = find_bb (cmB,ubB) BB in
    let votedA = mem_bb (cmA,ubA) BB in
    let votedB = mem_bb (cmB,ubB) BB in
    count(j) :=
      if  m = encr (<format iA, format kcA>) (pk_enc sk_mix2) seedA_enc2
      then (<format iA, format kcA>)
      else if m = encr (<format iB, format kcB>) (pk_enc sk_mix2) seedB_enc2
           then (<format iB, format kcB>)
           else decr m sk_mix2;
    unlock mutex_BB;
    unlock mutex_count
  ).


process mixer_vote_collect_CCA
  (cmA : message) (cmB : message)
  (pkAdmin : pk_sign)
=
  !_i (
    in(c,m);
    let m   = read m in
    let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
    let ubB =  unblind cmB pkAdmin tkB (read (input@Bvote))  in
    lock mutex_box;
    box(i):=
      if Avote < MVC(i) && m = encr zero_enc1 (pk_enc sk_mix1) seedA_enc1
      then (<cmA,format ubA>)
      else if Bvote < MVC(i) && m = encr zero_enc1 (pk_enc sk_mix1) seedB_enc1
      then (<cmB,format ubB>)
      else  decr m sk_mix1;
    unlock mutex_box
  ).


process mixer_open_collect_CCA
  (cmA,cmB : message) (kcA,kcB : k_comm) (pkAdmin : pk_sign)
=
  !_j(
    in(c,m);
    let m  = read m in
    let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
    let ubB = unblind cmB pkAdmin tkB (read (input@Bvote)) in
    lock mutex_BB;
    lock mutex_count;
    let iA = find_bb (cmA,ubA) BB in
    let iB = find_bb (cmB,ubB) BB in
    let votedA = mem_bb (cmA,ubA) BB in
    let votedB = mem_bb (cmB,ubB) BB in
    count(j) :=
      if  m = encr zero_enc2 (pk_enc sk_mix2) seedA_enc2
      then (<format iA, format kcA>)
      else if m = encr zero_enc2 (pk_enc sk_mix2) seedB_enc2
           then (<format iB, format kcB>)
           else decr m sk_mix2;
    unlock mutex_BB;
    unlock mutex_count
  ).


(* ------------------------------------------------------------------
## Process real and process cca-rewritten
------------------------------------------------------------------- *)

(* Randomness provided to the adversarial function `att'` *)
type att_rand[serializable,large].

name n_v0 : att_rand.
name n_v1 : att_rand.

name rdAdmin : att_rand.

abstract att' : att_rand -> message.

(*------------------------------------------------------------------*)
let v0 = att'(n_v0).
let v1 = att'(n_v1).
let pkAdmin : pk_sign = read (att'(rdAdmin)).

(*------------------------------------------------------------------*)
system Privacy_CCA =
  let vA  = diff(v0,v1) in
  let vB  = diff(v1,v0) in
  let kcA = diff(kc0,kc1) in
  let kcB = diff(kc1,kc0) in
  let cmA = comm vA kcA in
  let cmB = comm vB kcB in
  Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
  ( (A   : Alice_CCA (cmA,kcA,pkAdmin)                              )
  | (B   : Bob_CCA   (cmB,kcB,pkAdmin)                              )
  | (MVC : mixer_vote_collect_CCA(cmA,cmB,pkAdmin)                  )
  | (MVP : mixer_vote_publish                                       )
  | (BBS : set_BB                                                   )
  | (MOC : mixer_open_collect_CCA (cmA,cmB,kcA,kcB,pkAdmin)         )
  | (MOP : mixer_open_publish_CCA (pkAdmin,cmA,cmB)                 )
 ).


system Privacy_real =
  let vA  = diff(v0,v1) in
  let vB  = diff(v1,v0) in
  let kcA = diff(kc0,kc1) in
  let kcB = diff(kc1,kc0) in
  let cmA = comm vA kcA in
  let cmB = comm vB kcB in
  Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
  ( (A   : Alice_real (cmA,kcA,pkAdmin)                             )
  | (B   : Bob_real   (cmB,kcB,pkAdmin)                             )
  | (MVC : mixer_vote_collect_real(cmA,cmB,pkAdmin)                 )
  | (MVP : mixer_vote_publish                                       )
  | (BBS : set_BB                                                   )
  | (MOC : mixer_open_collect_real (cmA,cmB,kcA,kcB,pkAdmin)        )
  | (MOP : mixer_open_publish (pkAdmin,cmA,cmB,kcA,kcB)             )
 ).

(* compatibility check *)
global lemma [Privacy_CCA/left, Privacy_real/left] _ : [true].
Proof. auto. Qed.

(*------------------------------------------------------------------*)
(* Introduce a number of useful shorthands. *)

let cma @system:Privacy_CCA = comm diff(v0,v1) diff(kc0,kc1).
let cmb @system:Privacy_CCA = comm diff(v1,v0) diff(kc1,kc0).
let cm0 = comm v0 kc0.
let cm1 = comm v1 kc1.
let sA @system:Privacy_CCA : bsigned = read (input@Avote).
let sB @system:Privacy_CCA : bsigned = read (input@Bvote).
let uba = unblind cma pkAdmin tkA sA.
let ubb = unblind cmb pkAdmin tkB sB.
let ub0 @system:Privacy_CCA = unblind cm0 pkAdmin diff(tkA,tkB) diff(sA,sB).
let ub1 @system:Privacy_CCA = unblind cm1 pkAdmin diff(tkB,tkA) diff(sB,sA).
let bA = blind cma pkAdmin tkA.
let bB = blind cmb pkAdmin tkB.
let accA @system:Privacy_CCA = baccepte cma pkAdmin tkA sA.
let accB @system:Privacy_CCA = baccepte cmb pkAdmin tkB sB.
let acc_0 @system:Privacy_CCA = baccepte cm0 pkAdmin diff(tkA,tkB) diff(sA,sB).
let acc_1 @system:Privacy_CCA = baccepte cm1 pkAdmin diff(tkB,tkA) diff(sB,sA).
let bb_ @system:Privacy_CCA = BB@BBS.
let voteA = mem_bb (cma,uba) bb_.
let voteB = mem_bb (cmb,ubb) bb_.


(*******************************************************************************
## Restrictions : protocol phases

The protocles has 4 phases:
- Phase 1: obtain blind signatures of commits,
           send commits and their signatures to mix-net (C1: collect 1)
- Phase 2: publish the shuffle of all received commits (P1: publish 1),
           set the ballot box BB
- Phase 3: open commits, send commit keys to mix-net (C2: collect 2)
- Phase 4: publish the shuffle of all received commit keys (P2: publish 2)
********************************************************************************)

(* Trace restrictions.

   Phases are `1 < 2a < 2b < 3 < 4` where:
   - Phase 1: Avote, Bvote, MVC, Aauth, Bauth
   - Phase 2a: MVP
   - Phase 2b: BBS
   - Phase 3: MOC, Aopening, Bopening
   - Phase 4: MOP

   Each restriction comes in two flavors:
   - a positive version stating that some action `A` is before action
     `B` whenever `A` and `B` happens.
   - a negative version stating that `B` is never before `A` (here, it
     does not matter whether `B` or `A` happens)

   Restrictions are named depending on the order actions appears in,
   independently of whether they are positive or negative
   restrictions. E.g. `A_B` can be `happens(B) -> A < B` if this is a
   positive restriction, or `not (B < A)` if it is negative.

   Each time, we add at-most one of the two restriction as an axiom, and
   prove the second restriction from the first (i.e. we assume `A_B`,
   and prove `B_A` from it). *)
namespace Trace.
  (*------------------------------------------------------------------*)
  (* Miscellaneous *)

  (* W.l.o.g., we assume that the protocol was executed to its
    conclusion, thus that the opening phase concluded.
    Note that this does not entail that all action happened, as some
    action may not be scheduled (e.g. `MVC i` and `MOC i` may not happen
    for every `i`). *)
  axiom [any/Privacy_real] happens_MOP : happens(MOP).

  (* Similarly, we assume w.l.o.g. that `MVP` happens, as scheduling
    it provides some information to the adversary without requiring it
    to produce any input. *)
  axiom [any/Privacy_real] happens_MVP : happens(MVP).

  (* We assume that Alice and Bob always voted. *)
  axiom [any/Privacy_real] happens_Avote : happens(Avote).
  axiom [any/Privacy_real] happens_Bvote : happens(Bvote).

  (* We require that a value be published on the bulletin-board at the
     end of the voting phase. *)
  axiom [any/Privacy_real] happens_BBS : happens(BBS).

  (*------------------------------------------------------------------*)
  (* Phases 1/2 *)

  axiom [any/Privacy_real] MVC_MVP i : happens(MVC i) => MVC i < MVP.
  lemma [any/Privacy_real] MVP_MVC i : not (MVP < MVC i).
  Proof.
    intro H.
    have ? // := MVC_MVP i _.
  Qed.


  axiom [any/Privacy_real] MVC_BBS i : happens(MVC i) => MVC i < BBS.
  lemma [any/Privacy_real] BBS_MVC i : not (BBS < MVC i).
  Proof.
    intro H.
    have ? // := MVC_BBS i _.
  Qed.

  axiom [any/Privacy_real] Avote_MVP : happens(Avote) => Avote < MVP.
  lemma [any/Privacy_real] MVP_Avote : not (MVP < Avote).
  Proof.
    intro H.
    have ? // := Avote_MVP _.
  Qed.

  axiom [any/Privacy_real] Avote_BBS : happens(Avote) => Avote < BBS.
  lemma [any/Privacy_real] BBS_Avote : not (BBS < Avote).
  Proof.
    intro H.
    have ? // := Avote_BBS _.
  Qed.

  axiom [any/Privacy_real] Bvote_MVP : happens(Bvote) => Bvote < MVP.
  lemma [any/Privacy_real] MVP_Bvote : not (MVP < Bvote).
  Proof.
    intro H.
    have ? // := Bvote_MVP _.
  Qed.

  axiom [any/Privacy_real] Bvote_BBS : happens(Bvote) => Bvote < BBS.
  lemma [any/Privacy_real] BBS_Bvote : not (BBS < Bvote).
  Proof.
    intro H.
    have ? // := Bvote_BBS _.
  Qed.

  axiom [any/Privacy_real] Aauth_MVP : happens(Aauth) => Aauth < MVP.
  lemma [any/Privacy_real] MVP_Aauth : not (MVP < Aauth).
  Proof.
    intro H.
    have ? // := Aauth_MVP _.
  Qed.

  axiom [any/Privacy_real] Aauth_BBS : happens(Aauth) => Aauth < BBS.
  lemma [any/Privacy_real] BBS_Aauth : not (BBS < Aauth).
  Proof.
    intro H.
    have ? // := Aauth_BBS _.
  Qed.

  axiom [any/Privacy_real] Bauth_MVP : happens(Bauth) => Bauth < MVP.
  lemma [any/Privacy_real] MVP_Bauth : not (MVP < Bauth).
  Proof.
    intro H.
    have ? // := Bauth_MVP _.
  Qed.

  axiom [any/Privacy_real] Bauth_BBS : happens(Bauth) => Bauth < BBS.
  lemma [any/Privacy_real] BBS_Bauth : not (BBS < Bauth).
  Proof.
    intro H.
    have ? // := Bauth_BBS _.
  Qed.

  (*------------------------------------------------------------------*)
  (* Phases 2/3 *)

  axiom [any/Privacy_real] MVP_MOC i : happens(MOC i) => MVP < MOC i.
  lemma [any/Privacy_real] MOC_MVP i : not (MOC i < MVP).
  Proof.
    intro H.
    have ? // := MVP_MOC i _.
  Qed.

  axiom [any/Privacy_real] MVP_Aopening : happens(Aopening) => MVP < Aopening.
  lemma [any/Privacy_real] Aopening_MVP : not (Aopening < MVP).
  Proof.
    intro H.
    have ? // := MVP_Aopening _.
  Qed.

  axiom [any/Privacy_real] MVP_Bopening : happens(Bopening) => MVP < Bopening.
  lemma [any/Privacy_real] Bopening_MVP : not (Bopening < MVP).
  Proof.
    intro H.
    have ? // := MVP_Bopening _.
  Qed.

  axiom [any/Privacy_real] BBS_MOC i : happens(MOC i) => BBS < MOC i.
  lemma [any/Privacy_real] MOC_BBS i : not (MOC i < BBS).
  Proof.
    intro H.
    have ? // := BBS_MOC i _.
  Qed.

  axiom [any/Privacy_real] BBS_Aopening : happens(BBS,Aopening) => BBS < Aopening.
  lemma [any/Privacy_real] Aopening_BBS : not (Aopening < BBS).
  Proof.
    intro H.
    have ? // := BBS_Aopening _.
  Qed.

  axiom [any/Privacy_real] BBS_Bopening : happens(Bopening) => BBS < Bopening.
  lemma [any/Privacy_real] Bopening_BBS : not (Bopening < BBS).
  Proof.
    intro H.
    have ? // := BBS_Bopening _.
  Qed.

  (*------------------------------------------------------------------*)
  (* Phases */4 *)

  axiom [any/Privacy_real] any_MOP t : happens(t) => t <> MOP => t < MOP.
  lemma [any/Privacy_real] MOP_any t: t <> MOP => not (MOP < t).
  Proof.
    intro H.
    have ? // := any_MOP t.
  Qed.

  (*------------------------------------------------------------------*)
  (* Phases 1/3 *)

  lemma [any/Privacy_real] Avote_Aopening : happens(Aopening) => Avote < Aopening.
  Proof.
    intro H.
    have ? // := MVP_Aopening _.
    have ? // := Avote_MVP _.
  Qed.
  lemma [any/Privacy_real] Aopening_Avote : not (Aopening < Avote).
  Proof.
    intro H.
    have ? // := Avote_Aopening _.
  Qed.

  lemma [any/Privacy_real] Avote_Bopening : happens(Bopening) => Avote < Bopening.
  Proof.
    intro H.
    have ? // := MVP_Bopening _.
    have ? // := Avote_MVP _.
    apply happens_Avote.
  Qed.
  lemma [any/Privacy_real] Bopening_Avote : not (Bopening < Avote).
  Proof.
    intro H.
    have ? // := Avote_Bopening _.
  Qed.

  lemma [any/Privacy_real] Bvote_Aopening : happens(Aopening) => Bvote < Aopening.
  Proof.
    intro H.
    have ? // := MVP_Aopening _.
    have ? // := Bvote_MVP _.
    apply happens_Bvote.
  Qed.
  lemma [any/Privacy_real] Aopening_Bvote : not (Aopening < Bvote).
  Proof.
    intro H.
    have ? // := Bvote_Aopening _.
  Qed.

  lemma [any/Privacy_real] Bvote_Bopening : happens(Bopening) => Bvote < Bopening.
  Proof.
    intro H.
    have ? // := MVP_Bopening _.
    have ? // := Bvote_MVP _.
  Qed.
  lemma [any/Privacy_real] Bopening_Bvote : not (Bopening < Bvote).
  Proof.
    intro H.
    have ? // := Bvote_Bopening _.
  Qed.

  lemma [any/Privacy_real] MVC_Aopening i: happens(Aopening,MVC i) => MVC i < Aopening.
  Proof.
    intro H.
    have ? // := MVP_Aopening _.
    have ? // := MVC_MVP i _.
  Qed.
  lemma [any/Privacy_real] Aopening_MVC i: not (Aopening < MVC i).
  Proof.
    intro H.
    have ? // := MVC_Aopening i.
  Qed.

  lemma [any/Privacy_real] MVC_Bopening i: happens(Bopening,MVC i) => MVC i < Bopening.
  Proof.
    intro H.
    have ? // := MVP_Bopening _.
    have ? // := MVC_MVP i _.
  Qed.
  lemma [any/Privacy_real] Bopening_MVC i: not (Bopening < MVC i).
  Proof.
    intro H.
    have ? // := MVC_Bopening i.
  Qed.

   (*----------------------------------------------------------------*)
   (* within phase 2 *)

   axiom [any/Privacy_real] MVP_BBS : MVP < BBS.
   lemma [any/Privacy_real] BBS_MVP : not (BBS < MVP).
   Proof.
     intro H.
     have ? // := MVP_BBS.
   Qed.

   lemma [any/Privacy_real] rw_MVP_BBS :
     happens(MVP,BBS) => (MVP < BBS ) => MVP = pred BBS.
   Proof.
     intro Ham Leq.
     assert (forall t, happens(t) => t <= pred (BBS) => (t < MVP || t = MVP) ). {
       intro t.
       case t; intro Ht Eq.
       * auto.
       * intro H. left. by apply depends_Start_MVP.
       * intro H. left. by apply Trace.Aauth_MVP.
       * intro H. left. by apply Trace.Avote_MVP.
       * have N := Trace.Aopening_BBS. auto.
       * intro H. left. by apply Trace.Bauth_MVP.
       * intro H. left. by apply Trace.Bvote_MVP.
       * have N := Trace.Bopening_BBS. auto.
       * destruct Ht. intro H. left. rewrite Ceq. by apply ( Trace.MVC_MVP i).
       * intro H. right. auto.
       * intro H. have N : (not ( pred BBS < BBS)). auto. auto.
       * destruct Ht. intro H. rewrite Ceq.
         have N := (Trace.MOC_BBS j). auto.
       * have N := Trace.MOP_any BBS. auto.
     }.

     assert (forall t, happens(t) => (t = pred (BBS)) => (t = MVP) ). {
        intro t Ht Eq.
        assert t <= pred BBS as Neq by auto.
        have Aux :=  H t Ht Neq.
        case Aux; 2:auto.
        assert t < pred BBS.
        apply (lt_le_trans t MVP (pred BBS)).
        auto.
        auto.
        rewrite Eq in  Clt. auto.
     }.

     clear H.
     have hap : happens(pred BBS) by auto.
     have F := H0 (pred BBS) hap.
     auto.
  Qed.
end Trace.
