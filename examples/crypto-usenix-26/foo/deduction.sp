include Core.
include Libs.
include Games.
include[admit] processes.
include WeakSecrecy.
include[admit] shuffle.
include[admit] distinctEncryptions.
include[admit] distinctCommits.
include[admit] commitSecrecy.
include[admit] commitKeySecrecy.

(*------------------------------------------------------------------*)
let phiacc = accA && accB.
let phivote = voteA && voteB.


(******************************************************
# Direct shuffle opening deduction lemmas
*******************************************************)

global lemma [Privacy_CCA] open_box_ab  :
Let i_a = choose 
  (fun i => (input@MVC(i)) = 
    format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1)) 
in
Let a = diff(i_a,i_a) in
Let i_b = choose 
  (fun i => (input@MVC(i)) = 
     format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1)) 
in
Let b = diff(i_b,i_b) in 
Let Box = fun x => box(x)@pred(MVP) in 
Let f = diff(Box,Box) in 
Let open_cond = 
  not (commAB@MOP) && partial_injective Box (fun i => MVC i)
in
Let phi = diff(open_cond,open_cond) in
$(( 
    if phi
      then (fun j => ((j = a) || (j =  b)))
      else fun (j : index) => false,
    if phi then (a = b) else false,
    if phi then f a,
    if phi then f b,
    if phi 
      then (fun (j:index) => if (not (j = a || j =  b))
            then f j)
     else (fun (j:index) => zero),
    phi)
|>  (if phi then (shuffle f))).
Proof.
intro i_a a i_b b Box f open_cond phi.
apply open_shuffle.
Qed.

global lemma [Privacy_CCA] open_box_01  :
Let i_0 = choose 
  (fun i => (input@MVC(i)) = 
    format (encr zero_enc1 (pk_enc sk_mix1) diff(seedA_enc1,seedB_enc1))) 
in
Let a = diff(i_0,i_0) in
Let i_1 = choose 
  (fun i => (input@MVC(i)) = 
     format (encr zero_enc1 (pk_enc sk_mix1) diff(seedB_enc1,seedA_enc1))) 
in
Let b = diff(i_1,i_1) in 
Let Box = fun x => box(x)@pred(MVP) in 
Let f = diff(Box,Box) in
Let open_cond = 
  commAB@MOP &&  partial_injective Box (fun i => MVC i)
 in
Let phi = diff(open_cond,open_cond) in
$(( 
    if phi
      then (fun j => ((j = a) || (j =  b)))
      else fun (j : index) => false,
    if phi then (a = b) else false,
    if phi then f a,
    if phi then f b,
    if phi 
      then (fun (j:index) => if (not (j = a || j =  b))
            then f j)
     else (fun (j:index) => zero),
    phi)
|>  (if phi then (shuffle f))).
Proof.
intro i_0 a i_1 b  Box open_cond phi.
apply open_shuffle.
Qed.




global lemma [Privacy_CCA] open_count_01  :
Let i_0 = choose 
  (fun i => happens(MOC(i)) && input@MOC(i) = 
   format (encr zero_enc2 (pk_enc sk_mix2) diff(seedA_enc2,seedB_enc2)))
in
Let a = diff(i_0,i_0) in
Let i_1 = choose 
  (fun i => happens(MOC(i)) && input@MOC(i) = 
   format (encr zero_enc2 (pk_enc sk_mix2) diff(seedB_enc2,seedA_enc2))) 
in
Let b = diff(i_1,i_1) in
Let Count = fun x => count(x)@pred(MOP) in
Let f = diff(Count,Count) in
Let open_cond = 
   commAB@MOP && voteAB@MOP && partial_injective Count (fun i=> MOC i)
in
Let phi = diff(open_cond, open_cond) in 
[true] -> 
$(( 
    if phi
      then (fun j => ((j = a) || (j =  b)))
      else fun (j : index) => false,
    if phi then (a = b) else false,
    if phi then f a,
    if phi then f b,
    if phi 
      then (fun (j:index) => if (not (j = a || j =  b))
            then f j)
     else (fun (j:index) => zero),
    phi)
|>  (if phi then (shuffle f))).
Proof.
intro i_0 a i_1 b Count f open_cond phi ?.
apply open_shuffle.
Qed.


(*********************************************
# Deduction of partial injection lemmas
***********************************************)

lemma [any] forall2_eq (b,b':index -> index -> bool) :
  (forall i j , b i j = b' i j)  => ((forall i j, b i j) = (forall i j , b' i j)).
Proof.
  intro H.
  rewrite H.
  auto.
Qed. 

lemma [any] impl_eq (b0,b1,b2,b3 : bool) :
  (b0=b2) && (b0 => (b1 = b3)) => ( (b0 => b1) = (b2 => b3)).
Proof.
  intro [Hr Hl].
  by rewrite Hr Hl.
Qed.
 
global lemma [Privacy_CCA] rewrite_partial_inj_box :
Let Box = (fun x => box(x)@pred(MVP)) in
Let encA = encr zero_enc1 (pk_enc sk_mix1) seedA_enc1 in
Let encB = encr zero_enc1 (pk_enc sk_mix1) seedB_enc1 in
Let eqA = fun i => Avote < MVC(i) && read(input@MVC(i)) = encA in
Let eqB = fun i => Bvote < MVC(i) && read(input@MVC(i)) = encB in
[happens(MVP)] ->
[(partial_injective Box (fun i => MVC i)) = 
(forall (i,j:index), 
happens (MVC(i),MVC(j)) => 
( eqA i && eqA j) 
|| (eqB i && eqB j) 
|| ( (not (eqA i)) &&  (not (eqB i))
    && (not (eqA j)) && (not (eqB j))
    && decr (read (input@MVC(i))) sk_mix1 = decr (read (input@MVC(j))) sk_mix1) => i = j)
 ].
Proof.
intro Box encA encB eqA eqB Hap.
rewrite /partial_injective.
apply forall2_eq.
intro i j.
reduce.
apply impl_eq; split; 1:auto.
intro hap.
apply impl_eq; split; 2:auto.
have ? // := distinct_commit _.
have Encdiff := EncA1EncB1.diff_enc. 
rewrite eq_false in Encdiff.

assert (encA <> encA) = false as NeqA by rewrite -not_eq -eq_not.
assert (encB <> encB) = false as NeqB by rewrite -not_eq -eq_not.
rewrite /Box.
repeat rewrite Macro.box_val. auto. auto.
rewrite /box.
rewrite /m.
case eqA i;
case eqA j;
case eqB i;
case eqB j;
intro HjB HiB HjA  HiA ; simpl;
try (rewrite if_true; 1: auto);
try (rewrite if_false; 1: auto);
try (rewrite if_true; 1: auto);
try (rewrite if_false; 1: auto);
try (rewrite if_true; 1: auto);
try (rewrite if_false; 1: auto);
try (rewrite if_true; 1: auto);
try (rewrite if_false; 1: auto);
rewrite ?HiA ?HiB ?HjA ?HjB ?NeqA ?NeqB ?Encdiff //=.
* intro F. 
  apply f_apply fst in F. 
  simpl.
  have ? := localize(CommitSecrecy.Alice.secrecy (MVC j)) _; 
    1: by apply Trace.MVC_MVP. 
  auto.
* intro F. 
  apply f_apply fst in F. 
  simpl.
  have ? := localize(CommitSecrecy.Alice.secrecy (MVC i)) _; 
    1: by apply Trace.MVC_MVP. 
  auto.
* intro F. 
  apply f_apply fst in F. 
  simpl.
  have ? := localize(CommitSecrecy.Bob.secrecy (MVC j)) _; 
    1: by apply Trace.MVC_MVP. 
  auto.
* intro F. 
  apply f_apply fst in F. 
  simpl.
  have ? := localize(CommitSecrecy.Bob.secrecy (MVC i)) _; 
    1: by apply Trace.MVC_MVP. 
  auto.
Qed.

global lemma [Privacy_CCA] partial_inj_box_deduce :
Let Box = fun x => box(x)@pred(MVP) in
[happens(MVP)] ->
$( ((frame@pred(MVP)), sk_mix1, seedA_enc1,seedB_enc1) |> (partial_injective Box (fun i => MVC i))) .
Proof.
intro Box Hap. 
have H := rewrite_partial_inj_box _; 1:auto.
rewrite H. clear H. 
have -> :forall i j,  happens(MVC(i),MVC(j)) =
(happens(MVC(i),MVC(j)) && MVC(i) < MVP && MVC(j) < MVP ).
intro i j.
case happens(MVC(i),MVC(j)); 2:auto.
intro H.
simpl.
split.
by apply Trace.MVC_MVP i.
by apply Trace.MVC_MVP j.
reduce.
deduce ~all.
Qed.

lemma [Privacy_CCA] kcA_neq_kcB :
 happens Start =>
 format (kcA@Start) <> format (kcB@Start).
Proof.
  intro ? H.
  apply f_apply read[k_comm] in H. 
  rewrite !format_kc in H. 
  project; fresh H. 
Qed.

global lemma [Privacy_CCA] rewrite_partial_inj_count :
Let Count = fun x => count(x)@pred(MOP) in
Let encA = encr zero_enc2 (pk_enc sk_mix2) seedA_enc2 in
Let encB = encr zero_enc2 (pk_enc sk_mix2) seedB_enc2 in
[happens(MOP,BBS)] ->
[(partial_injective Count (fun i => MOC i)) = 
(forall (i,j:index), 
(happens(MOC(i),MOC(j)) =>((read (input@MOC(i)) = encA && (read (input@MOC(j))) = encA) 
|| ((read (input@MOC(i))) = encB && (read (input@MOC(j))) = encB) 
|| ((read (input@MOC(i))) <> encA && (read (input@MOC(i))) <> encB 
    && (read (input@MOC(j))) <> encA && (read (input@MOC(j))) <> encB 
    && decr (read (input@MOC(i))) sk_mix2 = decr (read (input@MOC(j))) sk_mix2)) => i = j))].
Proof.
intro Count encA encB Hap.
rewrite /partial_injective.
apply forall2_eq.
intro i j.
reduce.
apply impl_eq; split; 1:auto.
intro hap.
apply impl_eq; split; 2:auto.

have Encdiff := EncA2EncB2.diff_enc. 
rewrite eq_false in Encdiff.

assert (encA <> encA) = false as NeqA by rewrite -not_eq -eq_not.
assert (encB <> encB) = false as NeqB by rewrite -not_eq -eq_not.
rewrite /Count.
repeat rewrite Macro.count_val. auto. auto.
rewrite /count.
rewrite /m1.
case (read (input@MOC(i))) = encA;
case (read (input@MOC(j))) = encA;
case (read (input@MOC(i))) = encB;
case (read (input@MOC(j))) = encB;
intro HjB HiB HjA  HiA ; simpl;
try (rewrite if_true; 1: auto);
try (rewrite if_false; 1: auto);
try (rewrite if_true; 1: auto);
try (rewrite if_false; 1: auto);
try (rewrite if_true; 1: auto);
try (rewrite if_false; 1: auto);
try (rewrite if_true; 1: auto);
try (rewrite if_false; 1: auto);
rewrite ?HiA ?HiB ?HjA ?HjB ?NeqA ?NeqB ?Encdiff //=;
clear NeqA NeqB Encdiff HiA HiB HjA HjB;
clear. 
* rewrite /iA.
  have -> : BB@pred (MOC(i)) = BB@pred (MOC(j)). {

    rewrite -(Macro.bb_val (pred(MOC(i)))) //. {
      have h : (BBS < (MOC(i))) by apply (Trace.BBS_MOC i).
      constraints. 
    }. 
    rewrite -(Macro.bb_val (pred(MOC(j)))) //. {
      have h : (BBS < (MOC(j))) by apply (Trace.BBS_MOC j).
      constraints. 
    }. 
  }.
  auto.

* intro [? H].
  by have H0 := kcA_neq_kcB _.

* intro H.
  apply f_apply snd in H => /=.
  apply f_apply read[k_comm] in H.
  by apply CommitKeySecrecy.kcA_secrecy j.

* intro [? H].
  by have H0 := kcA_neq_kcB _. 

* intro H.
  apply f_apply snd in H => /=.
  apply f_apply read[k_comm] in H.
  by apply CommitKeySecrecy.kcA_secrecy i.

* rewrite /iB.
  have -> : BB@pred (MOC(i)) = BB@pred (MOC(j)). {

    rewrite -(Macro.bb_val (pred(MOC(i)))) //. {
      have h : (BBS < (MOC(i))) by apply (Trace.BBS_MOC i).
      constraints. 
    }. 
    rewrite -(Macro.bb_val (pred(MOC(j)))) //. {
      have h : (BBS < (MOC(j))) by apply (Trace.BBS_MOC j).
      constraints. 
    }. 
  }.
  auto.

* intro H.
  apply f_apply snd in H => /=.
  apply f_apply read[k_comm] in H.
  by apply CommitKeySecrecy.kcB_secrecy j.

* intro H.
  apply f_apply snd in H => /=.
  apply f_apply read[k_comm] in H.
  by apply CommitKeySecrecy.kcB_secrecy i.
Qed.



(*******************************************************************
# Opening shuffle lemmas
********************************************************************)

(*------------------------------------------------------------------*)
let phimix1 @system:Privacy_CCA =
      (exists i, happens(MVC(i)) && Avote < MVC(i) && (input@MVC(i)) =
        format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1))
   && (exists i, happens(MVC(i)) && Bvote < MVC(i) && (input@MVC(i)) =
       format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1)).

let phimix2 @system:Privacy_CCA =
      (exists i, happens(MOC(i)) && (input@MOC(i)) =
        format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2))
   && (exists i, happens(MOC(i)) && (input@MOC(i)) =
       format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2)).

(*------------------------------------------------------------------*)
global lemma [Privacy_CCA] deduce_mop_01 :
Let phi_in =  phivote && phimix1 && phiacc in
Let phi_out = phimix2 && phi_in in
Let rest = (sk_mix1,sk_mix2,seedA_enc2,seedB_enc2, 
            cm0, cm1, kc0,kc1,
           if accA && accB then ub0 else witness, 
           if accA && accB then ub1 else witness) in
Let fi0 =  (fun i => happens(MOC(i)) && (input@MOC(i)) = 
   format (encr zero_enc2 (pk_enc sk_mix2) diff(seedA_enc2,seedB_enc2))) in 
Let i_0 = choose fi0 in
Let fi1 = 
  (fun i => happens(MOC(i)) && (input@MOC(i)) = 
   format (encr zero_enc2 (pk_enc sk_mix2) diff(seedB_enc2,seedA_enc2))) 
in
Let i_1 = choose fi1 in
Let i_a = choose 
  (fun i => happens(MOC(i)) && (input@MOC(i)) = 
   format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2)) 
in
Let i_b = choose 
  (fun i => happens(MOC(i)) && (input@MOC(i)) = 
   format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2)) 
in
Let inp = fun j =>( input@MOC(j)) in
[happens(MVP,MOP,BBS)] -> 
$((
  rest,
  phi_in, phi_out,
  if phi_in then frame@pred MOP
)|> (
  if phi_out then (if  partial_injective (Count@MOP) (fun (i:index) => MOC(i)) then votes@MOP)
)).
Proof.
intro *.
rewrite /votes.
rewrite if_then_then. simpl.
set phi := _ && _.
set f := Count@MOP.

ghave OC : 
$(( 
    if phi
      then (fun j => ((j = i_0) || (j =  i_1)))
      else fun (j : index) => false,
    if phi then (i_0 = i_1) else false,
    if phi then f i_0,
    if phi then f i_1,
    if phi 
      then (fun (j:index) => if (not (j = i_0 || j =  i_1))
            then f j)
     else (fun (j:index) => zero),
    phi)
|>  (if phi then (shuffle f))).
{ have -> : phi = diff(phi,phi). by project.
  have -> : f = diff(f,f). by project.
  have -> : i_0 = diff(i_0,i_0). by project. 
  have -> : i_1 = diff(i_1,i_1). by project.
  apply open_shuffle.
}
deduce with OC.
clear OC.

have Rwor : forall j, (j = i_0 || j = i_1) = (j=i_a || j = i_b).
{ project; 1:auto.
  by rewrite or_comm.
}
rewrite Rwor.
rewrite Rwor.
clear Rwor.

have Rweq : ( i_0 = i_1) = (i_a  = i_b).
{ project; 1:auto.
  by rewrite (eq_sym i_0).
}
rewrite Rweq.
clear Rweq.

rewrite /phi.
set inj := partial_injective _ _.

have Hapi0 : 
(phi_out => 
happens(MOC(i_0)) && input@MOC(i_0) = 
format (encr zero_enc2 (pk_enc sk_mix2) diff(seedA_enc2,seedB_enc2))).
{ rewrite /phi_out /phimix2.
  intro [[Ha Hb] ?].
  have -> : (happens(MOC(i_0)) && input@MOC(i_0) = format (encr zero_enc2 (pk_enc sk_mix2) diff(seedA_enc2,seedB_enc2))) = fi0 i_0  by reduce.
  apply choose_ex.
  rewrite /fi0.
  reduce.
  by project; 1:apply Ha; apply Hb.
}

have Hapi1 : 
(phi_out => 
happens(MOC(i_1)) && input@MOC(i_1) = 
format (encr zero_enc2 (pk_enc sk_mix2) diff(seedB_enc2,seedA_enc2))).
{ rewrite /phi_out /phimix2.
  intro [[Ha Hb] ?].
  have -> : (happens(MOC(i_1)) && input@MOC(i_1) = format (encr zero_enc2 (pk_enc sk_mix2) diff(seedB_enc2,seedA_enc2))) = fi1 i_1  by reduce.
  apply choose_ex.
  rewrite /fi1.
  reduce.
  by project; 1:apply Hb; apply Ha.
}

have HiA : forall j,
(phi_out && inj => happens(MOC(j)) => (input@MOC(j)) = format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2) => j = diff(i_0,i_1)). 
{
  intro j [Hphiout  Hinj] Hapj F.
  assert (happens(MOC(diff(i_0,i_1)))) as Hapdiff.
  project.
    - have [h ?] := (localize(Hapi0) Hphiout).                
      apply  h.
    - have [h ?] := (localize(Hapi1) Hphiout).                
      apply  h.

  apply Hinj.
  reduce.
  split; auto.
  rewrite /Count. reduce.
  rewrite !Macro.count_val. auto. auto.
  rewrite /count.
  rewrite if_true. {
    rewrite /m1.
    rewrite F.
    auto.
  }
  rewrite if_true. {
    rewrite /m1.
    have [h0 r0]  := (localize(Hapi0) Hphiout).
    have [h1 r1] := (localize(Hapi1) Hphiout).
    project.
     - rewrite r0. by rewrite format_encr.
     - rewrite r1. by rewrite format_encr.
  }

  rewrite /iA.
  have -> : BB@pred(MOC(j)) = BB@BBS. {
    rewrite -Macro.bb_val. 
    have h : BBS < MOC(j) by apply Trace.BBS_MOC j.
    constraints. constraints.
    auto.
  }
  
  have -> : BB@pred(MOC(diff(i_0,i_1))) = BB@BBS. {
    rewrite -Macro.bb_val. 
    have h : BBS < MOC(diff(i_0,i_1)). apply Trace.BBS_MOC diff(i_0,i_1).
    apply Hapdiff.
    constraints. constraints. 
    auto.
  }        
  auto.
}

have HiB : forall j,
(phi_out && inj => happens(MOC(j)) => (input@MOC(j)) = format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2) => j = diff(i_1,i_0)). {
  intro j [Hphiout  Hinj] Hapj F.
  assert (happens(MOC(diff(i_1,i_0)))) as Hapdiff.
  project.
    - have [h ?] := (localize(Hapi1) Hphiout).                
      apply  h.
    - have [h ?] := (localize(Hapi0) Hphiout).                
      apply  h.

  apply Hinj.
  reduce.
  split. auto. auto.
  rewrite /Count. reduce.
  rewrite !Macro.count_val. auto. auto.
  rewrite /count.

  rewrite if_false.
  rewrite /m1.
  rewrite F.
  rewrite format_encr.
  rewrite eq_sym.
  project. 
  - by rewrite EncA2EncB2.diff_encL.
  - by rewrite EncA2EncB2.diff_encR. 

  rewrite if_true.
  rewrite /m1.
  rewrite F.
  auto. 

  rewrite if_false.
  rewrite /m1.
  have -> : input@MOC(diff(i_1,i_0)) = format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2). {
    have [? r0] := localize(Hapi0) Hphiout.
    have [? r1] := localize(Hapi1) Hphiout.
    project. by rewrite r1. by rewrite r0.
  }

  rewrite format_encr.
  rewrite eq_sym.
  project. 
  - by rewrite EncA2EncB2.diff_encL.
  - by rewrite EncA2EncB2.diff_encR. 

  rewrite if_true.
  rewrite /m1.
  have [? r0] := localize(Hapi0) Hphiout.
  have [? r1] := localize(Hapi1) Hphiout.
  project. by rewrite r1. by rewrite r0.
 
  rewrite /iB.
  have -> : BB@pred(MOC(j)) = BB@BBS. {
    rewrite -Macro.bb_val. 
    have h : BBS < MOC(j) by apply Trace.BBS_MOC j.
    constraints. constraints.
    auto.
  }
  
  have -> : BB@pred(MOC(diff(i_1,i_0))) = BB@BBS. {
    rewrite -Macro.bb_val. 
    have h : BBS < MOC(diff(i_1,i_0)). apply Trace.BBS_MOC diff(i_1,i_0).
    apply Hapdiff.
    constraints. constraints. 
    auto.
  }        
  auto.
}
  

have Rwfor : 
  forall j, 
    phi_out && inj => 
    not (j=i_a || j=i_b) => 
    (f j = if happens(MOC(j)) then decr (read (input@MOC(j))) sk_mix2 ). {
  intro j Hphioutinj Neq.
  rewrite not_or in Neq.
  destruct Neq as [Neqa Neqb].
  rewrite /f /Count /=.
  clear Hapi0 Hapi1; clear. 
  case (happens(MOC(j))); intro Ap.
  - simpl. 
    rewrite Macro.count_val;1: auto.
    rewrite /count if_false. {
      rewrite /m1.
      intro F.
      have hiA := (localize(HiA)) j Hphioutinj Ap.

      have ? : j=diff(i_0,i_1). {
        apply hiA.
        rewrite -F.
        by rewrite read_encr.
      }.
  
      have ? : not (j=diff(i_0,i_1)). {
        rewrite not_eq. 
        project; apply Neqa. 
      }.
      constraints.
    }.
  
    rewrite if_false. {
      rewrite /m1. 
      intro F.
      have hiB := (localize(HiB)) j Hphioutinj Ap.
  
      assert (j=diff(i_1,i_0)).
      apply hiB.
      rewrite -F.
      by rewrite read_encr.
   
      assert not (j=diff(i_1,i_0)) as F'.
      rewrite not_eq. project. apply Neqb. apply Neqb.
      constraints. 
    }.
    clear HiA HiB; clear.
    auto. 
  
  - clear HiA HiB; clear. 
    rewrite Macro.count_nan; 1,2: constraints. 
    by reduce. 
}.

clear HiA HiB.

set f0 := f i_0.
have -> : if phi_out && inj then f0 = 
          if phi_out && inj then (<format (find_bb (cm0,ub0) (BB@BBS)),format kc0>) . 
 { rewrite /f0 /f /Count. reduce.
   fa.
   intro [Hphiout Hinj].
   assert happens(MOC(i_0)) && input@MOC(i_0) = format (encr zero_enc2 (pk_enc sk_mix2) diff(seedA_enc2,seedB_enc2)) 
   by apply Hapi0.
   destruct H0.
   rewrite (Macro.count_val i_0). auto.
   rewrite /count.
   rewrite /m1.
   rewrite Meq.
   rewrite format_encr.
   project.
   - rewrite if_true. auto.
     rewrite /iA.
     have -> : BB@BBS = BB@(pred (MOC(i_0))).
     rewrite (Macro.bb_val (pred (MOC(i_0)))). 
     have h : BBS < (MOC(i_0)).  apply (Trace.BBS_MOC i_0).
     have [h ?]:= (localize(Hapi0)) Hphiout. apply h.
     constraints. constraints. constraints.
     auto.
   - rewrite if_false. 
     rewrite eq_sym.
     by rewrite EncA2EncB2.diff_encR.
     rewrite if_true. auto.
     rewrite /iB.
     have -> : BB@BBS= BB@(pred (MOC(i_0))).
     rewrite (Macro.bb_val (pred (MOC(i_0)))). 
     have h : BBS < (MOC(i_0)).  apply (Trace.BBS_MOC i_0).
     have [h ?]:= (localize(Hapi0)) Hphiout. apply h.
     constraints. constraints. constraints.
     
     auto.
  auto.
  }

set f1 := f i_1.
have -> : if phi_out && inj then f1 = 
          if phi_out && inj then (<format (find_bb (cm1,ub1) (BB@BBS)),format kc1>) . 
{ rewrite /f1 /f /Count. reduce.
   fa.
   intro [Hphiout Hinj].
   assert happens(MOC(i_1)) && input@MOC(i_1) = format (encr zero_enc2 (pk_enc sk_mix2) diff(seedB_enc2,seedA_enc2)) 
   by apply Hapi1.
   destruct H0.
   rewrite (Macro.count_val i_1). auto.
   rewrite /count.
   rewrite /m1.
   rewrite Meq.
   rewrite format_encr.
   project.
   - rewrite if_false.
     rewrite eq_sym.
     by rewrite EncA2EncB2.diff_encL.
     
     rewrite if_true. auto.

     rewrite /iB.
     have -> : BB@BBS = BB@(pred (MOC(i_1))).
     rewrite (Macro.bb_val (pred (MOC(i_1)))). 
     have h : BBS < (MOC(i_1)).  apply (Trace.BBS_MOC i_1).
     have [h ?]:= (localize(Hapi1)) Hphiout. apply h.
     constraints. constraints. constraints.
     auto.
   - rewrite if_true. auto.
     rewrite /iA.
     have -> : BB@BBS= BB@(pred (MOC(i_1))).
     rewrite (Macro.bb_val (pred (MOC(i_1)))). 
     have h : BBS < (MOC(i_1)).  apply (Trace.BBS_MOC i_1).
     have [h ?]:= (localize(Hapi1)) Hphiout. apply h.
     constraints. constraints. constraints.
     
     auto.
 auto.
}


rewrite Rwfor.
  intro j.
   intro ??. auto.
  intro j. intro [? ?] ?.
  auto.


have Rwmoc: 
forall i, input@(MOC(i)) = if happens(MOC(i)) then (if  MOC(i) < MOP then input@(MOC(i))) else empty. {
  intro i.
  case happens(MOC(i)); intro h.
  * simpl. 
    rewrite if_true.
    rewrite (Trace.any_MOP (MOC(i))). constraints. constraints. constraints. 
    auto.
  * simpl.
    by rewrite Macro.input_empty.
}
 
ghave IA : $((rest,phi_out, phi_in, if phi_in then frame@pred MOP) |> ((if phi_out then i_a else witness),(if phi_out then i_b else witness))). {
  rewrite /rest.
  rewrite /i_a.
  rewrite Rwmoc.
  deduce.  
  rewrite /i_b.
  rewrite Rwmoc.
  deduce ~all.
}


rewrite Rwmoc.
deduce with IA.
clear IA.

have -> : ((phi_out && inj) => (ub0 =  if accA && accB then ub0 else witness)). 
{ rewrite /phi_out /phi_in /phiacc.
  intro [[??? HaccA HaccB] ?].
  rewrite if_true.
  split. apply HaccA. apply HaccB.
  auto. 
}
auto. 

have -> : ((phi_out && inj) => (ub1  =  if accA && accB then ub1 else witness)). 
{ rewrite /phi_out /phi_in /phiacc.
  intro [[??? HaccA HaccB] ?].
  rewrite if_true.
  split. apply HaccA. apply HaccB.
  auto. 
}
auto.

rewrite /BB /bb.
have -> : input@BBS = if happens(BBS) then if BBS < MOP then input@BBS.
rewrite if_true. constraints.
rewrite if_true. apply Trace.any_MOP BBS. constraints.
constraints.
constraints.



ghave DeduceInj : 
$( (frame@pred(MOP), sk_mix2, seedA_enc2,seedB_enc2) |> 
   (inj)) .
{ have h := rewrite_partial_inj_count _.
  constraints.
  rewrite /inj.  
  rewrite h. clear h. 
  have Rin :forall i j,  
    happens(MOC(i),MOC(j))=
    (happens(MOC(i)) && happens(MOC(j))
    && MOC(i) < MOP && MOC(j) < MOP). 
  { intro i j.
    case happens(MOC(i));
    case happens(MOC(j));
    intro apj;
    intro api;
    try (reduce; constraints).
    rewrite (Trace.any_MOP (MOC(i))).
    constraints.
    apply api.
    rewrite (Trace.any_MOP (MOC(j))).
    constraints.
    apply apj.
    reduce. 
    constraints.
   }
   rewrite Rin.
   deduce ~all.
}

rewrite /(|>) in DeduceInj.    
destruct DeduceInj as [finj Rinj].
rewrite -Rinj.     
deduce ~all.
Qed.

lemma input_mvc_val {P : system[like Privacy_CCA]} @system:P i:
  input@MVC i = if happens(MVC i) then (if MVC i < MVP then input@MVC i) else empty.
Proof.
  case happens (MVC i) => Hap /=.
  - have ?// := Trace.MVC_MVP i _. 
    by rewrite if_true.
  - by rewrite Macro.input_empty.
Qed.

global lemma [Privacy_CCA] deduce_mvp_ab :
Let phia =
      (exists i, happens(MVC(i)) && Avote < MVC(i) && (input@MVC(i)) =
        format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1))  
in
Let phib =  (exists i, happens(MVC(i)) && Bvote < MVC(i) && (input@MVC(i)) = 
       format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1))
in
Let rest = 
    (sk_mix1,sk_mix2,seedA_enc1,seedB_enc1,cma,cmb,tkA,tkB,pkAdmin)
in
Let fia = (fun i => happens(MVC(i)) && Avote < MVC(i) && (input@MVC(i)) = 
   format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1)) 
in
Let i_a = choose fia in
Let fib = fun i => happens(MVC(i)) && Bvote < MVC(i) && (input@MVC(i)) = 
   format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1) 
in
Let i_b = choose fib
in
Let inp = fun j =>( input@MVC(j)) in
[happens(MVP,MOP,BBS)] -> 
$((
rest,
frame@pred MVP
)|> (if  partial_injective (Box@MVP) (fun (i:index) => MVC(i)) then commits@MVP)) .
Proof.
intro *.
rewrite /commits.
set phi := partial_injective _ _.
set f := Box@MVP.


have Hapia : 
(phia => 
happens(MVC(i_a)) && Avote < MVC(i_a) && input@MVC(i_a) = 
format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1)).
{ rewrite /phia.
  intro Ha.
  have -> : 
  (happens(MVC(i_a)) && Avote < MVC(i_a) && input@MVC(i_a)
   = format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1)) = fia i_a.
  rewrite /fia.
  by reduce.
  apply choose_ex.
  rewrite /fia.
  reduce.
  by apply Ha.
}

have Hapib : 
(phib => 
happens(MVC(i_b)) && Bvote < MVC(i_b) &&  input@MVC(i_b) = 
format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1)).
{ rewrite /phib.
  intro Hb.
  have -> : (happens(MVC(i_b)) && Bvote < MVC(i_b) && input@MVC(i_b) = format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1)) = fib i_b.
  rewrite /fib.
  by reduce.
  apply choose_ex.
  rewrite /fib.
  reduce.
  by apply Hb.
}

ghave DeduceSplit : 
$( (rest,frame@pred MVP) |>
   (phia,phib,phi,
    if (phia && phib && phi) then shuffle f, 
    if (not(phia) && phib && phi) then shuffle f,
    if (phia && not(phib) && phi) then shuffle f,
    if (not(phia) && not(phib) && phi) then shuffle f)). {
  
  ghave Deduce11 : 
  $(( 
     if (phia && phib && phi)
       then (fun j => ((j = i_a) || (j =  i_b)))
       else fun (j : index) => false,
      if (phia && phib && phi) then (i_a = i_b) else false,
      if (phia && phib && phi) then f i_a,
      if (phia && phib && phi) then f i_b,
      if (phia && phib && phi) 
        then (fun (j:index) => if (not (j = i_a || j =  i_b))
             then f j)
        else (fun (j:index) => zero),
      (phia && phib && phi))
   |>  (if (phia && phib && phi) then (shuffle f))). {
    
    have -> : (phia && phib && phi) = 
         diff((phia && phib && phi),(phia && phib && phi)).
    by project.
    have -> : f = diff(f,f). by project.
    have -> : i_a = diff(i_a,i_a). by project. 
    have -> : i_b = diff(i_b,i_b). by project.
    apply open_shuffle.
  }
  deduce with Deduce11.
  clear Deduce11.
  
  ghave Deduce01 : 
  $(( 
     if (not(phia) && phib && phi)
       then (fun j => ((j = i_b) || (j =  i_b)))
       else fun (j : index) => false,
      if (not(phia) && phib && phi) then (i_b = i_b) else false,
      if (not(phia) && phib && phi) then f i_b,
      if (not(phia) && phib && phi) then f i_b,
      if (not(phia) && phib && phi) 
        then (fun (j:index) => if (not (j = i_b || j =  i_b))
             then f j)
        else (fun (j:index) => zero),
      (not(phia) && phib && phi))
   |>  (if (not(phia) && phib && phi) then (shuffle f))). {
    
    have -> : (not(phia) && phib && phi) = 
         diff((not(phia) && phib && phi),(not(phia) && phib && phi)).
    by project.
    have -> : f = diff(f,f). by project.
    have -> : i_b = diff(i_b,i_b). by project. 
    apply open_shuffle.
  }
  deduce with Deduce01.
  clear Deduce01.

  ghave Deduce10 : 
  $(( 
     if (phia && not(phib) && phi)
       then (fun j => ((j = i_a) || (j =  i_a)))
       else fun (j : index) => false,
      if (phia && not(phib) && phi) then (i_a = i_a) else false,
      if (phia && not(phib) && phi) then f i_a,
      if (phia && not(phib) && phi) then f i_a,
      if (phia && not(phib) && phi) 
        then (fun (j:index) => if (not (j = i_a || j =  i_a))
             then f j)
        else (fun (j:index) => zero),
     (phia && not(phib) && phi))
   |>  (if (phia && not(phib) && phi) then (shuffle f))). {
    
    have -> : (phia && not(phib) && phi) = 
         diff((phia && not(phib) && phi),(phia && not(phib) && phi)).
    by project.
    have -> : f = diff(f,f). by project.
    have -> : i_a = diff(i_a,i_a). by project. 
    apply open_shuffle.
  }
  deduce with Deduce10.
  clear Deduce10.
  
  simpl.
  
  ghave Deducephiab : 
  $((rest,frame@pred MVP,phia,phib,phi) |> 
   (if phia && phi then i_a else witness,
    if phib && phi then i_b else witness,
    if phia && phi then f i_a,
    if phib && phi then f i_b)).

   set f_a := f i_a.
   have -> : if phia && phi then f_a = 
             if phia && phi then (<cma,format uba>) . 
   { rewrite /f_a /f /Box. reduce.
     fa.
     intro [Hpiha Hinj].
     assert happens(MVC(i_a)) && Avote < MVC(i_a) && input@MVC(i_a) 
     = format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1) as [H0 H1 H2]
     by apply Hapia.
     rewrite (Macro.box_val i_a). auto.
     rewrite /box.
     rewrite /m.
     rewrite H1 H2.
     by rewrite format_encr.
     auto.
   }
   
   
   set f_b := f i_b.
   have -> : if phib && phi then f_b = 
             if phib && phi then (<cmb,format ubb>) . 
   { rewrite /f_b /f /Box. reduce.
     fa.
     intro [Hpihb Hinj].
     assert happens(MVC(i_b)) && Bvote < MVC(i_b) && input@MVC(i_b)
        = format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1) as [H0 H1 H2]
     by apply Hapib.
     rewrite (Macro.box_val i_b). auto.
     rewrite /box.
     rewrite /m.
     rewrite H1 H2.
     rewrite format_encr. simpl.
     rewrite if_false. 
     rewrite eq_sym.
     print EncA1EncB1.diff_encR.
     project.
     by rewrite EncA1EncB1.diff_encL.
     by rewrite EncA1EncB1.diff_encR.
     auto.
     auto.
   }

  
   (* rewrite /i_a. *)
   (* rewrite /fia. *)
   (* rewrite /i_b. *)
   (* rewrite /fib. *)
   (* reduce. *)
   
   have Rwmvc: forall i, input@(MVC(i)) = if happens(MVC(i)) then (if  MVC(i) < MVP then inp i) else empty. {
   intro i.
   case happens(MVC(i)); intro h.
   * simpl. 
     rewrite if_true.
     rewrite (Trace.MVC_MVP (i)). constraints. constraints. 
     rewrite /inp. by reduce.
   * simpl.
     by rewrite Macro.input_empty.
}
   rewrite /i_a /fia.
   rewrite Rwmvc.
   deduce.
   rewrite /i_b /fib.
   rewrite Rwmvc. 
   deduce.

   rewrite /uba /sA.
   have -> : input@Avote = if happens(Avote) then (
   if Avote <  MVP then input@Avote) else empty.
   case happens(Avote); intro h.
   - simpl.
     rewrite if_true.
     by apply Trace.Avote_MVP. auto.
   - simpl.    
     by rewrite Macro.input_empty.

   rewrite /ubb /sB.
   have -> : input@Bvote = if happens(Bvote) then (
   if Bvote <  MVP then input@Bvote) else empty.
   case happens(Bvote); intro h.
   - simpl.
     rewrite if_true.
     by apply Trace.Bvote_MVP. auto.
   - simpl.    
     by rewrite Macro.input_empty.  
  
    deduce ~all.


  deduce with Deducephiab. 

  have HiA : forall j,
  (phia && phi => happens(MVC(j)) => Avote < MVC(j) => (input@MVC(j)) = format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1) => j = i_a). {
    intro j [Hphiout  Hinj] Hapj Hleq F.
    assert (happens(MVC(i_a))) as Hapdiff.
    project.
      - have [h ?] := (localize(Hapia) Hphiout).               
        by apply  h.
      - have [h ?] := (localize(Hapia) Hphiout).               
       by  apply  h.

    apply Hinj.
    reduce.
    split; auto.
    rewrite /Box. reduce.
    rewrite !Macro.box_val. constraints. constraints.
    rewrite /box.
    rewrite if_true. {
      rewrite /m.
      rewrite F.
      auto.
   }
   rewrite if_true. {
     rewrite /m.
     have [h0 r0]  := (localize(Hapia) Hphiout).
     have [h1 r1] := (localize(Hapia) Hphiout).
     project.
      - destruct r0 as [leq r0].
        rewrite leq r0. 
        by rewrite format_encr.
      - destruct r1 as [leq r1].
        rewrite leq r1. 
        by rewrite format_encr.
    }
   auto.
   }


  have HiB : forall j,
  (phib && phi => happens(MVC(j)) => Bvote < MVC(j) => (input@MVC(j)) = format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1) => j = i_b). {
    intro j [Hphiout  Hinj] Hapj Hleq F.
    assert (happens(MVC(i_b))) as Hapdiff.
    project.
      - have [h ?] := (localize(Hapib) Hphiout).               
        by apply  h.
      - have [h ?] := (localize(Hapib) Hphiout).               
        by apply  h.

    apply Hinj.
    reduce.
    split. auto. auto.
    rewrite /Box. reduce.
    rewrite !Macro.box_val. auto. auto.
    rewrite /box.

    rewrite if_false.
    rewrite /m.
    rewrite F.
    rewrite format_encr.
    rewrite eq_sym.
    project. 
      - by rewrite EncA1EncB1.diff_encL.
      - by rewrite EncA1EncB1.diff_encR. 

    rewrite if_true.
    rewrite /m.
    rewrite F.
    auto. 

    rewrite if_false.
    rewrite /m.
    have -> : input@MVC(i_b) = format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1). {
      have [? r0] := localize(Hapib) Hphiout.
      have [? r1] := localize(Hapib) Hphiout.
      project. 
        - destruct r1 as [leq r1] .
          by rewrite  r1. 
        - destruct r0 as [leq r0]. 
          by rewrite r0.
    }

    rewrite format_encr.
    rewrite eq_sym.
    project. 
      - by rewrite EncA1EncB1.diff_encL.
      - by rewrite EncA1EncB1.diff_encR. 

    rewrite if_true.
    rewrite /m.
    have [? r0] := localize(Hapib) Hphiout.
    have [? r1] := localize(Hapib) Hphiout.
    project. 
      - destruct r1 as [leq r1] .
        by rewrite  r1. 
      - destruct r0 as [leq r0]. 
        by rewrite r0.
        
    auto.
  }
 
  have Rwfor11 : 
   forall j, 
   phia && phib && phi => not (j=i_a || j=i_b) => 
   (f j = if happens(MVC(j)) then decr (read (input@MVC(j))) sk_mix1 ). 
  { intro j [Hphia Hphib Hinj] Neq.
    rewrite not_or in Neq.
    destruct Neq as [Neqa Neqb].
    rewrite /f /Box. reduce.
    case (happens(MVC(j))); intro Ap.
    simpl. 
    rewrite Macro.box_val. auto.
    rewrite /box.
    rewrite if_false.
    { rewrite /m.
      intro [Leq F].
      have h : (phia && phi). split. apply Hphia. apply Hinj.
      have hiA := (localize(HiA)) j h Ap.
      clear h.

      assert (j=i_a).
      apply hiA.
      apply Leq.
      rewrite -F.
      by rewrite read_encr.
 
    assert not (j = i_a) as F'.
    rewrite not_eq. project. apply Neqa. apply Neqa.
    constraints.
  } 

  rewrite if_false.
  { rewrite /m. 
    intro [Leq F]. 
    have h : (phib && phi). split. apply Hphib. apply Hinj.
    have hiB := (localize(HiB)) j h Ap.

    assert (j=i_b).
    apply hiB.
    apply Leq.
    rewrite -F.
    by rewrite read_encr.
 
    assert not (j=i_b) as F'.
    rewrite not_eq. project. apply Neqb. apply Neqb.
    constraints. 
  }
  
  auto. 

  rewrite Macro.box_nan; 1,2:constraints. 
  by reduce.
}.

rewrite Rwfor11; 1,2: constraints.
rewrite input_mvc_val /=. 
clear.

deduce with Deducephiab.

 
have Rwfor01 : 
  forall j, 
    not(phia) && phib && phi => 
    not (j=i_b || j=i_b) => 
    (f j = if happens(MVC(j)) then decr (read (input@MVC(j))) sk_mix1 ). 
{
  intro j [Hphia Hphib Hinj] Neq.
  rewrite not_or in Neq.
  destruct Neq as [Neqa Neqb].
  rewrite /f /Box. reduce.
  case (happens(MVC(j))); intro Ap.
  - simpl. 
    rewrite Macro.box_val. auto.
    rewrite /box.
    rewrite if_false. {
      rewrite /phia in Hphia.
      intro [Leq F].
      apply Hphia.
      exists j.
      split; 1: constraints. 
      rewrite /m in F.
      rewrite -F. 
      by rewrite read_encr.
    }.
  
    rewrite if_false. {
      rewrite /m. 
      intro [Leq F]. 
      have h : (phib && phi). { split. apply Hphib. apply Hinj. }.
      have hiB := (localize(HiB)) j h Ap.
  
      assert (j=i_b). {
        apply hiB.
        apply Leq.
        rewrite -F.
        by rewrite read_encr.
      }.
  
      have ?: not (j=i_b). {
        rewrite not_eq. project; apply Neqb. 
      }.
      constraints. 
    }.
    clear HiA HiB Hapia Hapib; clear.  
    apply eq_refl.
  
  - rewrite Macro.box_nan; 1,2: constraints. 
    by rewrite if_false /=. 
}.

rewrite Rwfor01; 1,2: constraints. 
rewrite input_mvc_val /=. 
clear.

deduce with Deducephiab.

have Rwfor10 : forall j, phia && not(phib) && phi => not (j=i_a || j=i_a) => 
   (f j = if happens(MVC(j)) then decr (read (input@MVC(j))) sk_mix1 ). {
  intro j [Hphia Hphib Hinj] Neq.
  rewrite not_or in Neq.
  destruct Neq as [Neqa Neqb].
  rewrite /f /Box /=. 
  case (happens(MVC(j))); intro Ap.
  - simpl. 
    rewrite Macro.box_val. auto.
    rewrite /box.
    rewrite if_false. {
      rewrite /m.
      intro [Leq F].
      have h : (phia && phi). split. apply Hphia. apply Hinj.
      have hiA := (localize(HiA)) j h Ap.
      clear h.

      assert (j=i_a). {
        apply hiA.
        apply Leq.
        rewrite -F.
        by rewrite read_encr.
      }.
 
      assert not (j = i_a) as F'. {
        rewrite not_eq. 
        project; apply Neqa.
      }.
      constraints.
    }.

    rewrite if_false. {
      rewrite /m.
      intro [Leq F].
      apply Hphib.
      rewrite /phib.
      exists j.
      split; 1 :constraints. 
      rewrite -F.
      by rewrite read_encr.
    }.
    apply eq_refl.

  - rewrite Macro.box_nan; 1,2: constraints.
    clear. 
    rewrite if_false //=.
}.

rewrite Rwfor10; 1,2: constraints. 
rewrite input_mvc_val /=. 
clear.

deduce with Deducephiab.

have Rwfor00 : 
  forall j, 
   not(phia) && not(phib) && phi =>
   (f j = if happens(MVC(j)) then decr (read (input@MVC(j))) sk_mix1 ). {
  intro j [Hphia Hphib Hinj].
  rewrite /f /Box. reduce.
  case (happens(MVC(j))); intro Ap.
  - simpl. 
    rewrite Macro.box_val. auto.
    rewrite /box.
    rewrite if_false. {
      rewrite /m.
      intro [Leq F].
      apply Hphia.
      rewrite /phia.
      exists j.
      split; 1 :constraints. 
      rewrite -F.
      by rewrite read_encr.
    }.

  rewrite if_false. {
    rewrite /m.
    intro [Leq F].
    apply Hphib.
    rewrite /phib.
    exists j.
    split; 1 :constraints. 
    rewrite -F.
    by rewrite read_encr.
  }.
  apply eq_refl.

  - rewrite Macro.box_nan; 1,2: constraints.
    clear. 
    rewrite if_false //=.
}.

have -> : f = fun j => f j by rewrite /f /Box /=. 
rewrite Rwfor00; 1:constraints. 
rewrite input_mvc_val /=. 
clear.

deduce with Deducephiab.

ghave DeduceInj : 
$( (frame@pred(MVP), sk_mix1, seedA_enc1,seedB_enc1) |> 
   (phi)). {
  have h := rewrite_partial_inj_box _.
  constraints.
  rewrite /phi.  
  rewrite h. clear h. 
  have Rin :
    forall i j, happens(MVC(i),MVC(j)) = 
    (happens(MVC(i)) && happens(MVC(j)) 
    && MVC(i) < MVP && MVC(j) < MVP). {
    intro i j. clear Hapib Hapia HiA HiB Rwfor00 Rwfor01 Rwfor10 Rwfor11. clear.
    case happens(MVC(i)); 2:auto.
    case happens(MVC(j)); 2:auto.
    intro ??.
    reduce. 
    rewrite (Trace.MVC_MVP i); 1: constraints.
    rewrite (Trace.MVC_MVP j); 1: constraints.
    reduce; true.
  }.
 
  rewrite Rin. 
  reduce.
  deduce ~all. 
}.

deduce with DeduceInj.
rewrite /phia.
rewrite input_mvc_val /=. 
clear.

deduce.

rewrite /phib.
rewrite input_mvc_val /=. 

deduce ~all.
}.

have -> : phi = ((phia && phib && phi) ||
               (not(phia) && phib && phi) ||
               (phia && not(phib) && phi) ||
               (not(phia) && not(phib) && phi)). { 
   generalize phi phia phib => p a b.
   clear Hapia Hapib DeduceSplit; clear. 
   apply boolean_eq; split.
  - intro -> /=. auto. 
  - case a => ? /=.
    + by case b.
    + by case b.
}.
rewrite 3!-if_then_or.

deduce with DeduceSplit.
Qed.



global lemma [Privacy_CCA] deduce_mvp_01 :
Let phi_in =  phiacc in
Let phi_out = phimix1 && phi_in in
Let rest = (sk_mix1,sk_mix2,seedA_enc1,seedB_enc1,cm0,cm1,
            if accA && accB then ub0 else witness, 
            if accA && accB then ub1 else witness) in
Let fi0 =  (fun i => happens(MVC(i)) && diff(Avote,Bvote) < MVC(i) && (input@MVC(i)) = 
   format (encr zero_enc1 (pk_enc sk_mix1) diff(seedA_enc1,seedB_enc1))) in 
Let i_0 = choose  fi0
in
Let fi1 = 
  (fun i => happens(MVC(i)) && diff(Bvote,Avote) < MVC(i) && (input@MVC(i)) = 
   format (encr zero_enc1 (pk_enc sk_mix1) diff(seedB_enc1,seedA_enc1))) 
in
Let i_1 = choose fi1 in
Let i_a = choose 
  (fun i => happens(MVC(i)) && Avote < MVC(i) && (input@MVC(i)) = 
   format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1)) 
in
Let i_b = choose 
  (fun i => happens(MVC(i)) && Bvote < MVC(i) &&  (input@MVC(i)) = 
   format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1)) 
in
Let inp = fun j =>( input@MVC(j)) in
[happens(MVP,MOP,BBS)] -> 
$((
rest,
phi_in, phi_out,
if phi_in then frame@pred MVP
)|> (
if phi_out then (if  partial_injective (Box@MVP) (fun (i:index) => MVC(i)) then commits@MVP)
)).
Proof.
intro *.
rewrite /commits.
rewrite if_then_then. simpl.
set phi := _ && _.
set f := Box@MVP.

ghave OC : 
$(( 
    if phi
      then (fun j => ((j = i_0) || (j =  i_1)))
      else fun (j : index) => false,
    if phi then (i_0 = i_1) else false,
    if phi then f i_0,
    if phi then f i_1,
    if phi 
      then (fun (j:index) => if (not (j = i_0 || j =  i_1))
            then f j)
     else (fun (j:index) => zero),
    phi)
|>  (if phi then (shuffle f))).
{ have -> : phi = diff(phi,phi). by project.
  have -> : f = diff(f,f). by project.
  have -> : i_0 = diff(i_0,i_0). by project. 
  have -> : i_1 = diff(i_1,i_1). by project.
  apply open_shuffle.
}
deduce with OC.
clear OC.

have Rwor : forall j, (j = i_0 || j = i_1) = (j=i_a || j = i_b).
{ project; 1: auto.
  by rewrite or_comm.
}
rewrite Rwor.
rewrite Rwor.
clear Rwor.

have Rweq : ( i_0 = i_1) = (i_a  = i_b).
{ project; 1:auto.
  by rewrite (eq_sym i_0).
}
rewrite Rweq.
clear Rweq.

rewrite /phi.
set inj := partial_injective _ _.

have Hapi0 : 
(phi_out => 
happens(MVC(i_0)) && diff(Avote,Bvote) < MVC(i_0) && input@MVC(i_0) = 
format (encr zero_enc1 (pk_enc sk_mix1) diff(seedA_enc1,seedB_enc1))).
{ rewrite /phi_out /phimix1.
  intro [[Ha Hb] ?].
  have -> : (happens(MVC(i_0)) && diff(Avote,Bvote) < MVC(i_0) && input@MVC(i_0) = format (encr zero_enc1 (pk_enc sk_mix1) diff(seedA_enc1,seedB_enc1))) = fi0 i_0  by reduce.
  apply choose_ex.
  rewrite /fi0.
  reduce.
  by project; 1:apply Ha; apply Hb.
}

have Hapi1 : 
(phi_out => 
happens(MVC(i_1)) && diff(Bvote,Avote) < MVC(i_1) && input@MVC(i_1) = 
format (encr zero_enc1 (pk_enc sk_mix1) diff(seedB_enc1,seedA_enc1))).
{ rewrite /phi_out /phimix1.
  intro [[Ha Hb] ?].
  have -> : (happens(MVC(i_1)) && diff(Bvote,Avote) < MVC(i_1) && input@MVC(i_1) 
  = format (encr zero_enc1 (pk_enc sk_mix1) diff(seedB_enc1,seedA_enc1))) = fi1 i_1  by reduce.
  apply choose_ex.
  rewrite /fi1.
  reduce.
  by project; 1:apply Hb; apply Ha.
}

have HiA : forall j,
(phi_out && inj => happens(MVC(j)) => Avote < MVC(j) =>
 (input@MVC(j)) = format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1) => j = diff(i_0,i_1)). 
{
  intro j [Hphiout  Hinj] Hapj Leq F.
  assert (happens(MVC(diff(i_0,i_1)))) as Hapdiff.
  project.
    - have [h ?] := (localize(Hapi0) Hphiout).                
      by apply  h.
    - have [h ?] := (localize(Hapi1) Hphiout).                
      by apply  h.

  apply Hinj.
  reduce.
  split; auto.
  rewrite /Box. reduce.
  rewrite !Macro.box_val. constraints. constraints.
  rewrite /box.
  rewrite if_true. {
    rewrite /m.
    rewrite F.
    auto.
  }
  rewrite if_true. {
    rewrite /m.
    have [h0 [leq0 r0]]  := (localize(Hapi0) Hphiout).
    have [h1 [leq1 r1]] := (localize(Hapi1) Hphiout).
    project.
     - rewrite leq0 r0. by rewrite format_encr.
     - rewrite leq1 r1. by rewrite format_encr.
  }

  auto.
}

have HiB : forall j,
(phi_out && inj => happens(MVC(j)) => Bvote < MVC(j) =>
(input@MVC(j)) = format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1) => j = diff(i_1,i_0)). {
  intro j [Hphiout  Hinj] Hapj Leq F.
  assert (happens(MVC(diff(i_1,i_0)))) as Hapdiff.
  project.
    - have [h ?] := (localize(Hapi1) Hphiout).                
      by apply  h.
    - have [h ?] := (localize(Hapi0) Hphiout).                
      by apply  h.

  apply Hinj.
  reduce.
  split. auto. auto.
  rewrite /Box. reduce.
  rewrite !Macro.box_val. auto. auto.
  rewrite /box.

  rewrite if_false.
  rewrite /m.
  rewrite F.
  rewrite format_encr.
  rewrite eq_sym.
  project. 
  - by rewrite EncA1EncB1.diff_encL.
  - by rewrite EncA1EncB1.diff_encR. 

  rewrite if_true.
  rewrite /m.
  rewrite F.
  auto. 

  rewrite if_false.
  rewrite /m.
  have -> : input@MVC(diff(i_1,i_0)) = format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1). {
    have [? [leq0 r0]] := localize(Hapi0) Hphiout.
    have [? [leq1 r1]] := localize(Hapi1) Hphiout.
    project. by rewrite r1. by rewrite r0.
  }

  rewrite format_encr.
  rewrite eq_sym.
  project. 
  - by rewrite EncA1EncB1.diff_encL.
  - by rewrite EncA1EncB1.diff_encR. 

  rewrite if_true.
  rewrite /m.
  have [? [leq0 r0]] := localize(Hapi0) Hphiout.
  have [? [leq1 r1]] := localize(Hapi1) Hphiout.
  project. by rewrite r1. by rewrite r0.
 
  auto.
}
  

have Rwfor : forall j, phi_out && inj 
=> not (j=i_a || j=i_b) 
=> (f j = if happens(MVC(j)) then decr (read (input@MVC(j))) sk_mix1 ). 
{ intro j [Hphioutinj] Neq.
  rewrite not_or in Neq.
  destruct Neq as [Neqa Neqb].
  rewrite /f /Box. reduce.
  case (happens(MVC(j))); intro Ap.
  simpl. 
  rewrite Macro.box_val. auto.
  rewrite /box.
  rewrite if_false.
  { rewrite /m.
    intro [Leq F].
    have hiA := (localize(HiA)) j Hphioutinj Ap.

    assert (j=diff(i_0,i_1)).
    apply hiA. apply Leq.
    rewrite -F.
    by rewrite read_encr.
 
    assert not (j=diff(i_0,i_1)) as F'.
    rewrite not_eq. project. apply Neqa. apply Neqa.
    constraints.
  } 

  rewrite if_false.
  { rewrite /m. 
    intro [Leq F].
    have hiB := (localize(HiB)) j Hphioutinj Ap.

    assert (j=diff(i_1,i_0)).
    apply hiB.
    apply Leq.
    rewrite -F.
    by rewrite read_encr.
 
    assert not (j=diff(i_1,i_0)) as F'.
    rewrite not_eq. project. apply Neqb. apply Neqb.
    constraints. 
  }
  
  auto. 

  rewrite Macro.box_nan. auto. auto. auto.
}

clear HiA HiB.

set f0 := f i_0.
have -> : if phi_out && inj then f0 = 
          if phi_out && inj then (<cm0,format ub0>) . 
 { rewrite /f0 /f /Box. reduce.
   fa.
   intro [Hphiout Hinj].
   assert happens(MVC(i_0)) && diff(Avote,Bvote) < MVC(i_0) && input@MVC(i_0) 
   = format (encr zero_enc1 (pk_enc sk_mix1) diff(seedA_enc1,seedB_enc1)) as [H0 H1 H2]
   by apply Hapi0.
   rewrite (Macro.box_val i_0). auto.
   rewrite /box.
   rewrite /m.
   rewrite  H2.
   rewrite format_encr.
   project.
   - by rewrite if_true.     
   - rewrite if_false. 
     rewrite eq_sym.
     by rewrite EncA1EncB1.diff_encR.
     by rewrite if_true. 
  auto.
  }

set f1 := f i_1.
have -> : if phi_out && inj then f1 = 
          if phi_out && inj then (<cm1,format ub1>) . 
{ rewrite /f1 /f /Box. reduce.
   fa.
   intro [Hphiout Hinj].
   assert happens(MVC(i_1)) && diff(Bvote,Avote) < MVC(i_1) && input@MVC(i_1) 
   = format (encr zero_enc1 (pk_enc sk_mix1) diff(seedB_enc1,seedA_enc1)) as [H0 H1 H2]
   by apply Hapi1.
   rewrite (Macro.box_val i_1). auto.
   rewrite /box.
   rewrite /m.
   rewrite H2.
   rewrite format_encr.
   project.
   - rewrite if_false.
     rewrite eq_sym.
     by rewrite EncA1EncB1.diff_encL.
     by rewrite if_true.
   - by rewrite if_true.
 auto.
}


rewrite Rwfor.
  intro j.
   intro ??. auto.
  intro j. intro [? ?] ?.
  auto.


have Rwmoc: forall i, input@(MVC(i)) = if happens(MVC(i)) then (if  MVC(i) < MVP then input@MVC(i)) else empty. {
  intro i.
  case happens(MVC(i)); intro h.
  * simpl. 
    rewrite if_true.
    rewrite (Trace.MVC_MVP i). constraints. constraints.
    constraints.
  * simpl.
    by rewrite Macro.input_empty.
}
 
ghave IA : $((rest,phi_out, phi_in, if phi_in then frame@pred MVP) |> ((if phi_out then i_a else witness),(if phi_out then i_b else witness))). {
  rewrite /rest /i_a.
  rewrite Rwmoc.
  deduce.
  rewrite /i_b.
  rewrite Rwmoc.
  deduce ~all.
}

rewrite Rwmoc.
deduce with IA.
clear IA.


ghave DeduceInj : 
$( ( (frame@pred(MVP)),  sk_mix1, seedA_enc1,seedB_enc1) |> 
   ( inj )) .
{ have h := rewrite_partial_inj_box _.
  constraints.
  rewrite /inj.  
  rewrite h. clear h. 
  have Rin :forall i j,  
  happens(MVC(i),MVC(j)) = 
  (happens(MVC(i)) && happens(MVC(j)) 
   && MVC(i) < MVP && MVC(j) < MVP).

  { intro i j.
    case happens(MVC(i));
    case happens(MVC(j));
    intro apj;
    intro api;
    try (simpl; constraints). 
    simpl. 
    rewrite (Trace.MVC_MVP i).
    apply api.
    rewrite (Trace.MVC_MVP j).
    apply apj.
    constraints.  
 }
  rewrite  Rin. 
  set encA := encr _ _ _ .
  set encB := encr _ _ _ .
  reduce.
  deduce ~all.
}

rewrite /(|>) in DeduceInj.
destruct DeduceInj as [finj Rinj].
rewrite -Rinj.
deduce ~all.
Qed.




(*******************************************************************************
# Ready-to-apply openning shuffle lemmas
********************************************************************************)


global lemma [Privacy_CCA] deduce_shuffle_mvp_01 : 
Let phimix1 =
      (exists i, happens(MVC(i)) && Avote < MVC(i) && (input@MVC(i)) =
        format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1))  
   && (exists i, happens(MVC(i)) && Bvote < MVC(i) && (input@MVC(i)) = 
       format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1))
in
Let phimix2 =
      (exists i, happens(MOC(i)) && (input@MOC(i)) =
        format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2))  
   && (exists i, happens(MOC(i)) && (input@MOC(i)) = 
       format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2))
in
Let phi_out =  phimix1 && phiacc in
Let phi_in =  phiacc in
Let rest = 
    (sk_mix1,sk_mix2,seedA_enc1, seedB_enc1,v0,v1,rdAdmin,
     cm0,cm1, if acc_0 && acc_1 then ub0 else witness,
     if acc_0 && acc_1 then ub1 else witness, accA, accB) 
in
[happens(MOP,MVP,BBS)] -> 
$((rest,phimix1 && phi_in, phi_in, if phi_in then frame@pred MVP) 
|>
(if (phimix1 && phi_in) then
  (if partial_injective (Box@MVP) (fun (i:index) => MVC(i)) then commits@MVP))).
Proof.
intro *.
rewrite /rest.
have -> : (acc_0 && acc_1) = (accA && accB).
  project; 1:auto. by rewrite and_comm.
print deduce_mvp_01.
deduce with deduce_mvp_01; 1:auto.
Qed.

(*------------------------------------------------------------------*)
global lemma [Privacy_CCA] deduce_shuffle_mvp_ab : 
Let phi = phimix2 && phivote && phimix1 && phiacc in
Let rest = (sk_mix1,
   sk_mix2,
   seedA_enc1,
   seedA_enc2,
   seedB_enc1,
   seedB_enc2,
   pkAdmin,
   cma,
   cmb,
   tkA,
   tkB) 
in 
[happens(MVP,MOP,BBS)] -> 
$((rest) |>
(frame@pred MVP,
  if partial_injective (Box@MVP) (fun (i:index) => MVC(i)) then commits@MVP)).
Proof.
intro *.
deduce with deduce_mvp_ab; 1:auto.

ghave DeduceLoop : Forall (t:timestamp[const]), [t < MVP] -> ($((rest, frame@pred t) |> (frame@t))).
intro t Hleq.
clear.
induction t; try deduce.
 - have ? := Trace.Aopening_MVP. constraints.
 - have ? := Trace.Bopening_MVP. constraints.  
 - have ? := Trace.any_MOP (MVP). constraints.

ghave Deduce : Forall (t:timestamp[const]), [t < MVP] -> ($((rest) |> (frame@t))).
clear.
induction.
intro t Hind.
intro Hleq.
have C : (t = init) || (init < t). auto.
case C.
- rewrite C. deduce.
- have Ded := DeduceLoop t.
  have Hp := Hind (pred t).
  deduce with Ded.
  auto.
  apply Hp.
  auto.
  auto.

have DeduceMVP := Deduce (pred MVP).
apply DeduceMVP.
auto.
Qed.

(*------------------------------------------------------------------*)
global lemma [Privacy_CCA] deduce_shuffle_mop_01 : 
Let phimix1 =
      (exists i, happens(MVC(i)) && Avote < MVC(i) &&  (input@MVC(i)) =
        format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1))  
   && (exists i, happens(MVC(i)) && Bvote < MVC(i) && (input@MVC(i)) = 
       format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1))
in
Let phimix2 =
      (exists i, happens(MOC(i)) && (input@MOC(i)) =
        format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2))  
   && (exists i, happens(MOC(i)) && (input@MOC(i)) = 
       format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2))
in
Let phi_in =  phivote && phimix1 && phiacc in
Let phi_out = phimix2 && phi_in in
Let rest = (sk_mix1,
     sk_mix2,
     seedA_enc2,
     seedB_enc2,
     cm0,
     cm1,
     kc0,
     kc1,
     if (acc_0 && acc_1) then ub0 else witness,
     if (acc_0 && acc_1) then ub1 else witness)
 in
[happens(MVP,MOP,BBS)] -> 
$((rest, phi_in,
   phi_out,
   if phi_in then frame@pred MOP) |>
   (if phi_out then
  (if partial_injective (Count@MOP) (fun (i:index) => MOC(i)) then votes@MOP))).
Proof.
  intro *.
  rewrite /rest.
  have -> : (acc_0 && acc_1) = (accA && accB).
  project; 1:auto. by rewrite and_comm.
  deduce with deduce_mop_01. auto.
Qed.
