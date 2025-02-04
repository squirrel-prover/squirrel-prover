include Core.
include WeakSecrecy.
include Libs.
include Games.
include[admit] processes.
include[admit] macros.
include[admit] voteHiding.
include[admit] deduction.

(*------------------------------------------------------------------*)
set timeout=10.

(******************************************************************************
# Reduction of equiv to equiv without macros by bideduction
*******************************************************************************)


(*------------------------------------------------------------------*)
lemma exists_aux @system:any ['a] (phi, phi0 : 'a -> bool) :
  (forall x, phi0 x = (phi x && phi0 x)) =>
  (exists x, phi0 x) = (exists x, phi x && phi0 x).
Proof.
  intro H.
  rewrite H.
  apply eq_refl.
Qed.

lemma pair_aux @system:any ['a 'b] (x,x' : 'a) (y,y':'b) :
  x = x' => y = y' => (x,y) = (x',y').
Proof. auto. Qed.

(*------------------------------------------------------------------*)
global lemma [Privacy_CCA] deduction_p2_01 :
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
     if (acc_0 && acc_1) then ub1 else witness) in
[happens(MVP,MOP,BBS)] -> 
$((
rest,
phi_in,
if phi_in then frame@pred MOP
)|> (
phi_out,
if phi_out then frame@MOP
)).
Proof.
intro ??? Hap.

ghave DeducePhi: 
 $((
   rest,
   phi_in,
   if phi_in then frame@pred MOP
  ) |> (
   phi_in && phimix2 
  )).
{
  rewrite /phimix2.
  rewrite (Macro.rw_cond_input_moc (fun i => (MOC(i) < MOP))). {
    intro i hphi h.
    reduce.
    by rewrite (Trace.any_MOP _); 1,2: constraints.
  }

  (* hack to make sure we rewrite the second exists *)
  set p := (exists _, _). rewrite (and_comm p).
  
  rewrite (Macro.rw_cond_input_moc (fun i => (MOC(i) < MOP))). {
    intro i hphi h.
    reduce.
    by rewrite (Trace.any_MOP _); 1,2: constraints.
  }
  reduce.
  rewrite -(and_comm p) /p => {p}.
  deduce.
}.

ghave DeduceFrame: 
  $(( rest, phi_in, 
      if phi_in then frame@pred MOP, phimix2 && phi_in)
   |>
   (if phimix2 && phi_in then frame@MOP )).
{
  ghave DeduceOutput:
  $(( rest,phimix2 && phi_in, phi_in, 
      if phi_in then frame@pred MOP
   )|>  (if phimix2 && phi_in then output@MOP )).
  {
    rewrite /output.
 
    have -> :(commAB@MOP && voteAB @MOP) = (phimix2 && phi_in) .
    {  
      rewrite eq_sym.
      rewrite /phi_in.
      rewrite /phivote.
      rewrite /voteA.
      rewrite (Macro.bb_val (pred MOP)); 
      [1: have ? := Trace.any_MOP BBS; 1:constraints |
       2: constraints].
      rewrite /voteB. 
      rewrite (Macro.bb_val (pred MOP));
      [1: have ? := Trace.any_MOP BBS; 1:constraints |
       2: constraints].
       
      apply boolean_eq.

      (* What follows could be replaced by `auto`,
         but that would be slower. *)
      split. 
      + intro A; split.
        rewrite /commAB. split; 1: auto. split; 1: auto. 
        by split.
        rewrite /voteAB. split; 1: auto. split; 1: auto. by split.
      + intro [A0 [? [? [A1 A2]]]]; split.
        rewrite /phimix2. split; 1: auto. auto.
        split; 2:split; 1:split. 
        rewrite /* in A1, A2.
        rewrite /*.
        rewrite A1.
        rewrite A2.
        constraints. 
        auto. auto. 
        rewrite /phiacc; by split. 
    }.
    rewrite -if_then_push.
    apply deduce_shuffle_mop_01. auto.
  }. 
  rewrite /frame.
  rewrite Macro.exec_val; 1: constraints.
  deduce with DeduceOutput.
}.
(* Manual proof of transitivity. *)
rewrite /(|>) in DeducePhi.
destruct DeducePhi as [fphi hphi].

rewrite /(|>) in DeduceFrame.
destruct DeduceFrame as [fframe hframe].
rewrite /(|>).
exists fun x =>
  let phio = (fphi x) in
 (phio, (fframe (x#1,x#2,x#3,phio))).
reduce.
rewrite hphi.
rewrite and_comm.
rewrite hframe.
apply pair_aux; 1: apply eq_refl. 
case (phi_out = true).
+ intro -> /=. true.
+ smt ~no_macros.
Qed.

(*------------------------------------------------------------------*)
global lemma [Privacy_CCA] deduction_p1_01 :
Let phi_out =  phimix1 && phiacc in
Let phi_in =  phiacc in
Let rest = (sk_mix1,sk_mix2,seedA_enc1,seedB_enc1,v0,v1,rdAdmin,
            cm0, cm1, accA, accB,
            if acc_0 && acc_1 then ub0 else witness,
            if acc_0 && acc_1 then ub1 else witness) 

in
[happens(MVP,MOP,BBS)] -> 
$((rest, phi_in, if phi_in then frame@pred MVP )
|> (
phi_out, if phi_out then frame@MVP
)).
Proof.
intro ??? Hap.

ghave DeducePhi: 
 $((
  rest,
  phi_in,
  if phi_in then frame@pred MVP
 )|>(
  phimix1 && phi_in )). 
{
  rewrite (and_if phimix1 phi_in).
  rewrite /phimix1.

  have Rew : 
     forall i, input@MVC(i) = 
               if happens(MVC(i)) then (if MVC(i) < MVP then input@MVC(i)) else empty. 
  {
    intro i.
    case happens(MVC i); intro hc /=.
    + rewrite if_true; 1: have ? := Trace.MVC_MVP i; constraints.
      apply eq_refl.
    + by apply Macro.input_empty.
  }.

  ghave DeducePhiA : 
  $((
    rest, phi_in, if phi_in then frame@pred MVP
   )|>(
    if phi_in 
    then (exists i, happens(MVC(i)) && Avote < MVC(i) && input@MVC(i) = format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1))
    else false
   )) 
  by rewrite Rew; deduce.
  
  ghave DeducePhiB : 
  $((
   rest, phi_in, if phi_in then frame@pred MVP
  )|>(
   if phi_in 
   then (exists i, happens(MVC(i)) && Bvote < MVC(i) && input@MVC(i) = format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1))
   else false
  )) 
  by rewrite Rew; deduce.

  rewrite /(|>) in DeducePhiA.
  destruct DeducePhiA as [fphia hphia].
   
  rewrite /(|>) in DeducePhiB.
  destruct DeducePhiB as [fphib hphib].
 
  rewrite /(|>).
  exists
    fun (x:(sk_enc * sk_enc * seed * seed* _ * _ * _ * _ * _ * bool *bool * signed * signed) * bool * _) =>
     let phiin = (x#2) in
     if phiin then ((fphia x) && (fphib x)) else false.
  rewrite /= hphia hphib.
  fa; try auto.
  intro Hphiin.   
  rewrite if_true; 1:auto.
  rewrite if_true; 1:auto.
  apply eq_refl.
}.

ghave DeduceFrame: 
   $(( rest, phi_in, 
       if phi_in then frame@pred MVP, phimix1 && phi_in)
     |>  (if phimix1 && phi_in then frame@MVP )).

    ghave DeduceOutput:
    $(( phimix1 && phi_in, phi_in, rest,
        if phi_in then frame@pred MVP
     )|>  (if phimix1 && phi_in then output@MVP )).
{
  rewrite /output.
  by apply deduce_shuffle_mvp_01.
}.
     
rewrite /frame.
rewrite Macro.exec_val; 1: constraints.
deduce with DeduceOutput.

(* Manual proof of transitivity. *)
rewrite /(|>) in DeducePhi.
destruct DeducePhi as [fphi hphi].
 
rewrite /(|>) in DeduceFrame.
destruct DeduceFrame as [fframe hframe].
rewrite /(|>).
exists 
  fun x =>
    let phio = (fphi x) in
    (phio, (fframe (x#1,x#2,x#3,phio))).
rewrite /= hphi hframe //.
Qed.



global lemma [Privacy_CCA] deduction_ab :
Let phi = phimix2 && phivote && phimix1 && phiacc in
[happens(MVP,MOP,BBS)] -> 
$( (sk_mix1, sk_mix2,
    seedA_enc1,seedA_enc2, 
    seedB_enc1, seedB_enc2,
    pkAdmin,
    cma, cmb,
    tkA, tkB, 
    v0,v1,rdAdmin) 
|> (phi,
    if not phi then frame@MOP)).
Proof.
intro ? Hap.
ghave DeduceFrame:
Forall (t:_[const]), [happens(t)] -> [t < MOP] ->
$( (sk_mix1, sk_mix2,
   seedA_enc1,seedA_enc2,
   seedB_enc1, seedB_enc2,
   pkAdmin,
   cma, cmb,
   tkA, tkB)
|> (frame@t)).
{
  intro t Ht Hmop.
  induction t; try apply IH.
  * deduce.
  * rewrite /frame.
    rewrite Macro.exec_val; 1: constraints.
    simpl.
    rewrite /output. rewrite /acc. rewrite /voted.
    rewrite /sb.
    rewrite /pkAdmin.
    rewrite Macro.bb_aopening. auto.
    rewrite /BB /bb.
    apply IH.
  * rewrite /frame.
    rewrite Macro.exec_val; 1: constraints.
    simpl.
    rewrite /output. rewrite /acc1. rewrite /voted1.
    rewrite /sb1.
    rewrite /pkAdmin.
    rewrite Macro.bb_bopening. auto.
    rewrite /BB /bb.
    apply IH.
  * rewrite /frame.
    rewrite /output.
    rewrite Macro.exec_val; 1:auto.
    simpl.
    apply deduce_shuffle_mvp_ab. auto.
}.

ghave Ha : [happens(pred(MOP))] by auto.
ghave Hl : [pred MOP < MOP] by auto.

have DeducePred := DeduceFrame (pred(MOP)) Ha Hl. 
clear Ha Hl DeduceFrame.
rewrite /frame /output Macro.exec_val; 1: constraints.

rewrite /= (if_false ((commAB@MOP) && (voteAB@MOP))). {
  rewrite -impl_contra /commAB /voteAB.
  intro [[hmix1A hmix1B hacc] [hmix2A hmix2B hvoteA hvoteB]].
  rewrite /phi. 
  repeat split; try auto.
  * rewrite /votedA1 in hvoteA. 
    rewrite -(Macro.bb_val (pred MOP)) in hvoteA. 
    have ? := Trace.any_MOP BBS; constraints. 
    constraints. 
    auto.
  * rewrite /votedB1 in hvoteB. 
    rewrite -(Macro.bb_val (pred MOP)) in hvoteB. 
    have ? := Trace.any_MOP BBS; constraints. 
    constraints. 
    auto.
}.

rewrite /= /phi /phimix2 /phivote /phiacc /phimix1.

have Rewmvc : 
  forall i, 
    input@MVC(i) = 
    if happens(MVC(i)) then (if MVC(i) < MOP then input@MVC(i)) else empty. 
{
  intro i.
  case happens(MVC(i)); intro hap. 
  rewrite /= if_true; 2:auto.
  have ? := Trace.any_MOP (MVC i); constraints. 
  simpl. 
  by apply Macro.input_empty.
}.

(* annoying manipulation to avoid circular rewriting *)
set a1 := exists i, happens(MVC(i)) && Avote < MVC(i) && input@MVC i = _.
set a2 := exists i, happens(MVC(i)) && Bvote < MVC(i) && input@MVC i = _.
revert a1.
rewrite Rewmvc.
revert a2.
rewrite Rewmvc.
intro a1 a2; rewrite /a1 /a2 => {a1} {a2} {Rewmvc}.

set a1 := exists i, happens(MOC(i)) && input@MOC i = _.
set a2 := exists i, happens(MOC(i)) && input@MOC i = _.
have Rewmoc : 
  forall i, 
    input@MOC(i) = 
    if happens(MOC(i)) then (if MOC(i) < MOP then input@MOC(i)) else empty. 
{
  intro i. 
  case happens(MOC(i)); intro hap. 
  rewrite /= if_true; 2:auto. 
  have ? := Trace.any_MOP (MOC i); constraints. 
  simpl. 
  by apply Macro.input_empty.
}.

(* annoying manipulation to avoid circular rewriting *)
revert a1.
rewrite Rewmoc.
revert a2.
rewrite Rewmoc.
intro a1 a2; rewrite /a1 /a2 => {a1} {a2} {Rewmoc}.

rewrite /=. 

rewrite /accA /accB /voteA /voteB /uba /ubb.
rewrite /sA /sB.
have -> : 
  input@Avote = 
  if happens(Avote) then if Avote < MOP then input@Avote else empty else empty.
{
  case happens(Avote); intro hap => //.
  rewrite if_true0 if_true; 2:auto.
  have ? := Trace.any_MOP Avote; constraints. 
  rewrite if_false0. 
  by apply Macro.input_empty.
}.

have -> : 
  input@Bvote = 
  if happens(Bvote) then if Bvote < MOP then input@Bvote else empty else empty. 
{
  case happens(Bvote); intro hap => //.
  rewrite if_true0 if_true; 2:auto.
  have ? := Trace.any_MOP Bvote; constraints. 
  rewrite if_false0. 
  by apply Macro.input_empty.
}.

rewrite /bb_ /BB /bb.
have -> : input@BBS = if BBS < MOP then input@BBS else empty.
{ 
  rewrite if_true; 2:auto. 
  have ? := Trace.any_MOP BBS; constraints. 
}.

deduce with DeducePred.
Qed.



(*------------------------------------------------------------------*)
global lemma [Privacy_CCA] reduction_full :
Let phi = phimix2 && phivote && phimix1 && phiacc in
Let restr2 =  (sk_mix1,
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
Let restc2 =  (seedA_enc2,seedB_enc2, sk_mix2,cm0,cm1,
               if acc_0 && acc_1 then ub0 else witness, 
               if acc_0 && acc_1 then ub1 else witness)  in  
Let restr1 =(sk_mix1,sk_mix2,seedA_enc1,seedB_enc1,v0,v1,rdAdmin,
            cm0, cm1, accA, accB,
            if acc_0 && acc_1 then ub0 else witness,
            if acc_0 && acc_1 then ub1 else witness) 

in
Let restc1 =  (sk_mix1,sk_mix2,seedA_enc1,seedB_enc1,bA,bB,accA,accB,v0,v1,rdAdmin) in
[happens(MVP,MOP,BBS)] -> equiv(frame@MOP).
Proof.
intro ????? Hap.
rewrite (if_push_add phi).
cs phi.

* (* If phi holds, opening in 01 order. *)

  (*---------------------------------*)
  (** `reducing from P2 to C2`: 
      phi3, if phi3 then u3 |> phi4 then u4 *)
  ghave H:
    $( ((restr2, phivote && phimix1 && phiacc,
        if  phivote && phimix1 && phiacc then (frame@pred MOP))) 
    |> (phimix2 && phivote && phimix1 && phiacc,
        if phimix2 && phivote && phimix1 && phiacc then frame@MOP))
    by apply deduction_p2_01 Hap.

  deduce with H.
  clear H.

  (*---------------------------------*)
  (** `reducing from C2 to P1`: 
      phi2, if phi2 then u2 |> phi3 then u3 *) 
  ghave H:
  Forall (t:_[const]), [MVP <= t] -> [t < MOP] ->  
  $( ( (restc2, phimix1 && phiacc,
   if phimix1 && phiacc then frame@MVP)) 
   |> (  phivote && phimix1 && phiacc,
  if  phivote && phimix1 && phiacc then frame@t
  )).
  {
  intro t hmvp hmop.
  ghave DeducePhi:  
    $( ( (restc2, phimix1 && phiacc,
    if phimix1 && phiacc then frame@MVP)) 
    |> (  phivote && phimix1 && phiacc)).
    { 
     have -> : (phivote && phimix1 && phiacc) = if (phimix1 && phiacc) then phivote else false.
     by case (phimix1&& phiacc).
     rewrite /phivote.
     have -> : if phimix1 && phiacc then (voteA && voteB) else false =
               if phimix1 && phiacc then 
               ((mem_bb (cm0,(if acc_0 && acc_1 then ub0 else witness)) (BB@BBS)) && 
                (mem_bb (cm1,if acc_0 && acc_1 then ub1 else witness) (BB@BBS)))
               else false. 
     { case phimix1 && phiacc; intro Hc; try auto.
       simpl.  
       rewrite if_true. by project.
       rewrite if_true. by project.
       project; 1: auto. 
       by rewrite and_comm.
     }. 
     ghave C: [BBS < MVP || MVP < BBS ]. auto.    
     case C.
     -- deduce ~all.
     -- rewrite Macro.bb_val_mvp. auto. auto. deduce ~all.
    }.

  ghave DeduceFrame:
  $( (restc2, phimix1&&phiacc, if phimix1 && phiacc then frame@MVP, phivote && phimix1 && phiacc) |>
     (if phivote && phimix1 && phiacc then frame@t)). 
  induction t. 
  - by deduce.

  - depends Start, MVP; 1:auto. 
    intro ?; constraints.

  - (* [MVP < Aauth < MOP]: impossible *)
    have ? := Trace.Aauth_MVP _; 1: constraints.
    constraints.

  - (* [MVP < Avote < MOP]: impossible *)
    have ? := Trace.Avote_MVP _; 1: constraints.
    constraints.

  - (* [MVP < Aopening < MOP] *)
    ghave C : [MVP < pred Aopening || (MVP = pred Aopening)]. {
      have ? := Trace.Aopening_MVP. 
      constraints.
    }.
    case C.
    + rewrite /frame. 
      rewrite !Macro.exec_val; try constraints. 
      simpl.
      rewrite /output.
      rewrite (if_true (acc@Avote && voted@Aopening)).
      rewrite /phivote.
      rewrite /voteA.
      rewrite (Macro.bb_val Aopening); 2:auto. {
        have A := Trace.BBS_Aopening _; 1: constraints. 
        constraints.
      }. 
      auto.
      rewrite /frame in IH.
      rewrite !Macro.exec_val in IH; try constraints.
      deduce with  IH.

    + rewrite C.
      rewrite /frame.
      rewrite !Macro.exec_val; try constraints.
      rewrite /= /output.
      rewrite (if_true (acc@Avote && voted@Aopening)). {
        rewrite /phivote.
        rewrite /voteA.
        rewrite (Macro.bb_val Aopening); 2:auto. {
          have A := Trace.BBS_Aopening _; 1: constraints.
          constraints.
        }.
        intro *. by split.
      }.
      deduce.

  - (* [MVP < Bauth < MOP]: impossible *)
    have ? := Trace.Bauth_MVP _; 1: constraints.
    constraints.

  - (* [MVP < Bvote < MOP]: impossible *)
    have ? := Trace.Bvote_MVP _; 1: constraints.
    constraints.

  - ghave C: [MVP < pred Bopening || (MVP = pred Bopening)]. {
      have ? := Trace.Bopening_MVP.
      constraints.
    }.
    case C.
    + rewrite /frame.
      rewrite !Macro.exec_val; try constraints.
      simpl.
      rewrite /output.
      rewrite (if_true ((acc1@Bvote) && voted1@Bopening)). {
        rewrite /phivote.
        rewrite /voteB.
        rewrite (Macro.bb_val Bopening); 2:auto. {
           have A := Trace.BBS_Bopening _; 1: constraints.
           constraints.
        }.
        intro *. by split.
      }.
      rewrite /frame in IH.
      rewrite !Macro.exec_val in IH; try constraints.
      deduce with IH.

    + rewrite C.
      rewrite /frame.
      rewrite !Macro.exec_val; try constraints.
      rewrite /= /output.
      rewrite (if_true (acc1@Bvote && voted1@Bopening)). {
        rewrite /phivote.
        rewrite /voteB.
        rewrite (Macro.bb_val Bopening); 2:auto. {
          have A := Trace.BBS_Bopening _; 1: constraints.
          constraints.
        }.
        intro *. by split.
      }.
      deduce.

  - (* [MVP < MVC i < MOP]: impossible *)
    have ? := Trace.MVC_MVP i.
    constraints.

  - (* [MVP <= MVP < MOP] *)
    deduce.

  - (* [MVP < BBS < MOP] *)
    have -> : frame@BBS =  <frame@(pred BBS),<of_bool true,output@BBS>>. {
      rewrite /frame.
      rewrite !Macro.exec_val; try constraints.
      by rewrite /output .
    }.
    simpl.
    have rw : MVP = pred BBS by apply Trace.rw_MVP_BBS; constraints.
    rewrite -rw.
    deduce ~all.

  - (* [MVP < MOC j < MOP] *)
    ghave C: [MVP < (pred (MOC(j))) || (MVP = pred (MOC(j)))]. {
       have ? := Trace.MOC_MVP.
       constraints.
    }.
    case C.
    + by deduce with IH.
    + have -> :
        frame@(MOC(j)) =
        <frame@(pred (MOC(j))),<of_bool (exec@(MOC(j))), if (exec@MOC(j)) then output@(MOC(j))>>
      by auto.

      rewrite !Macro.exec_val; try constraints.
      rewrite /output.
      rewrite -C.
      deduce ~all.

  - (* [MVP < MOP < MOP] *)
    constraints.

  (* Manual proof of transitivity. *)
  rewrite /(|>) in DeducePhi.
  destruct DeducePhi as [fphi hphi].

  rewrite /(|>) in DeduceFrame.
  destruct DeduceFrame as [fframe hframe].

  rewrite /(|>).
  exists fun x =>
    let phio = (fphi x) in
    (phio, (fframe (x#1,x#2,x#3,phio))).
  reduce.
  rewrite hphi.
  rewrite hframe.
  auto.
  }.

  deduce with H (pred MOP) _ _; 1: auto. {
    have A := Trace.any_MOP MVP _ _; 1,2:constraints.
    search pred _ .
    by rewrite le_pred_lt.
  }.
  clear H.

  (*---------------------------------*)
  (** `reducing from P1 to C1`:
      phi1, if phi1 then u1 |> phi2 then u2 *)
  ghave H:
    $( (restr1, phiacc,
        if  phiacc then frame@pred MVP)
    |> (phimix1 && phiacc,
        if  phimix1 && phiacc then frame@MVP)).
  have h:= deduction_p1_01 Hap.
  deduce with h.

  deduce with H.
  clear H.

  (*---------------------------------*)
  (** `reducing from C1 to /`:
      phi1, if phi1 then u1 |> phi2 then u2 *)
  ghave H:
    Forall (t:_[const]), [ t < MVP] ->
    $( restc1
    |> (phiacc,
        if phiacc then frame@t) ).
  {
  intro t hmvp.
  ghave DeducePhi:
    $(restc1 |> phiacc)
    by deduce.
  ghave DeduceFrame:
  $( (restc1,phiacc) |>
     (if phiacc then frame@t) ).
  induction t.
   - by deduce.
   - by apply IH.
   - by apply IH.
   - rewrite /frame.
     rewrite Macro.exec_val; 1:constraints.
     rewrite /output.
     simpl.
     rewrite (if_true (acc@Avote)). auto.
     by apply IH.
   - have ? := Trace.Aopening_MVP.
     constraints.
   - by apply IH.
   - rewrite /frame.
     rewrite Macro.exec_val; 1:constraints.
     rewrite /output.
     simpl.
     rewrite (if_true (acc1@Bvote)). auto.
     by apply IH.
   - have ? := Trace.Bopening_MVP.
     constraints.
   - apply IH.
   - constraints.
   - have ?:= Trace.BBS_MVP. constraints.
   - have ? := Trace.MOC_MVP j.
     constraints.
   - have ? := Trace.any_MOP MVP _ _; constraints.

  (* Manual proof of transitivity *)

  rewrite /(|>) in DeducePhi.
  destruct DeducePhi as [fphi hphi].

  rewrite /(|>) in DeduceFrame.
  destruct DeduceFrame as [fframe hframe].

  rewrite /(|>).
  exists fun x =>
    let phio = (fphi x) in
    (phio, (fframe ((x),phio))).
  reduce.
  rewrite hphi.

  rewrite hframe.
  auto.
  }.

  deduce with H (pred MVP) _; 1: auto.
  clear H.
  rewrite /restr2 /restc1.
  clear.
  by apply blinding.

* (* Otherwise, opening in ab order. *)
  have H := deduction_ab Hap.
  deduce with H.
  clear H.
  clear.
  apply voteHiding.
Qed.

(*------------------------------------------------------------------*)
set timeout=1.
