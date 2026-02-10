include Core.
include Libs.
include Games.
include WeakSecrecy.
include[admit] processes.
include[admit] macros.


include[admit] ccapk1.
include[admit] ccapk2.

global lemma [any/Privacy_real] deduce_frame (t,t':timestamp[const]) : 
[t <= t'] -> $( (frame@t') |> (frame@t)).
Proof.
intro Ht.
induction t;try deduce.
Qed.


global lemma [any/Privacy_real] deduce_input_pred_MVP_Avote : 
[happens(MVP,Avote)] -> 
$( (frame@pred MVP) |> (input@Avote)).
Proof.
intro Hap.
assert (Avote < MVP) by apply (Trace.Avote_MVP).
have HDed := (deduce_frame Avote (pred MVP)).
assert Avote <= pred MVP by constraints.
apply HDed in H0.
rewrite /input.
deduce with H0.
Qed.


global lemma [any/Privacy_real] deduce_input_pred_MOP_Avote : 
[happens(MOP,Avote)] -> 
$( (frame@pred MOP) |> (input@Avote)).
Proof.
intro Hap.
assert (Avote < MOP)  by apply (Trace.any_MOP Avote).
have HDed := (deduce_frame Avote (pred MOP)).
assert Avote <= pred MOP by constraints.
apply HDed in H0.
rewrite /input.
deduce with H0.
Qed.

global lemma [any/Privacy_real] deduce_input_pred_Aopening_BBS : 
[happens(Aopening,BBS)] -> 
$( (frame@pred Aopening) |> (input@BBS)).
Proof.
intro Hap.
assert (BBS < Aopening) by apply Trace.BBS_Aopening.
have HDed := (deduce_frame BBS (pred Aopening)).
assert BBS <= pred Aopening by constraints.
apply HDed in H0.
rewrite /input.
deduce with H0.
Qed.

global lemma [any/Privacy_real] deduce_input_pred_MVP_Bvote : 
[happens(MVP,Bvote)] -> 
$( (frame@pred MVP) |> (input@Bvote)).
Proof.
intro Hap.
assert (Bvote < MVP) by apply (Trace.Bvote_MVP).
have HDed := (deduce_frame Bvote (pred MVP)).
assert Bvote <= pred MVP by constraints.
apply HDed in H0.
rewrite /input.
deduce with H0.
Qed.


global lemma [any/Privacy_real] deduce_input_pred_MOP_Bvote : 
[happens(MOP,Bvote)] -> 
$( (frame@pred MOP) |> (input@Bvote)).
Proof.
intro Hap.
assert (Bvote < MOP) by apply (Trace.any_MOP Bvote).
have HDed := (deduce_frame Bvote (pred MOP)).
assert Bvote <= pred MOP by constraints.
apply HDed in H0.
rewrite /input.
deduce with H0.
Qed.

global lemma [any/Privacy_real] deduce_input_pred_Bopening_BBS : 
[happens(Bopening,BBS)] -> 
$( (frame@pred Bopening) |> (input@BBS)).
Proof.
intro Hap.
assert (BBS < Bopening) by apply Trace.BBS_Bopening.
have HDed := (deduce_frame BBS (pred Bopening)).
assert BBS <= pred Bopening by constraints.
apply HDed in H0.
rewrite /input.
deduce with H0.
Qed.

global lemma [any/Privacy_real] deduce_input_pred_MOP_BBS : 
[happens(MOP,BBS)] -> 
$( (frame@pred MOP) |> (input@BBS)).
Proof.
intro Hap.
assert (BBS < MOP) by apply Trace.any_MOP BBS.
have HDed := (deduce_frame BBS (pred MOP)).
assert BBS <= pred MOP by constraints.
apply HDed in H0.
rewrite /input.
deduce with H0.
Qed.

global lemma [any/Privacy_real] deduce_input_pred_MVP_MVC : 
[happens(MVP)] -> 
$( (frame@pred MVP) |> (fun i => (input@MVC(i)))).
Proof.
intro Hap.
have Rew : 
forall i, input@MVC(i) = 
if happens(MVC(i)) then (if MVC(i) < MVP then input@MVC(i)) else empty.
{ intro i. 
  rewrite Macro.rw_input.
  case happens(MVC(i)); try auto.
  intro Hapi. 
  simpl.
  rewrite if_true.  by apply Trace.MVC_MVP.
  auto.
}
rewrite Rew.
deduce.
Qed.

global lemma [any/Privacy_real] deduce_input_pred_MOP_MVC : 
[happens(MOP)] -> 
$( (frame@pred MOP) |> (fun i => (input@MVC(i)))).
Proof.
intro Hap.
have Rew : 
forall i, input@MVC(i) = 
if happens(MVC(i)) then (if MVC(i) < MOP then input@MVC(i)) else empty.
{ intro i. 
  rewrite Macro.rw_input.
  case happens(MVC(i)); try auto.
  intro Hapi. 
  simpl.
  rewrite if_true.  by apply (Trace.any_MOP (MVC(i))).
  auto.
}
rewrite Rew.
deduce.
Qed.

global lemma [any/Privacy_real] deduce_input_pred_MOP_MOC : 
[happens(MOP)] -> 
$( (frame@pred MOP) |> (fun i => (input@MOC(i)))).
Proof.
intro Hap.
have Rew : 
forall i, input@MOC(i) = 
if happens(MOC(i)) then (if MOC(i) < MOP then input@MOC(i)) else empty.
{ intro i. 
  rewrite Macro.rw_input.
  case happens(MOC(i)); try auto.
  intro Hapi. 
  simpl.
  rewrite if_true.  by apply (Trace.any_MOP (MOC(i))).
  auto.
}
rewrite Rew.
deduce.
Qed.


namespace SwitchLeftRealPK1.

lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left]
box_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MVC i <= t =>
  box(i)@ t = box(i)@MVC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MVC i; 1: auto.
  intro Hmc.
  case t < MVC i; 1: constraints.
  intro Hleq.
  have Hp := H (pred t).
  rewrite !impl_true in Hp; 1,2,3: constraints.
  have -> : box(i)@t = box(i)@pred t. {
    case t; intro Ht => //.
    destruct Ht as [i0 Ceq].
    case i = i0; 1: auto.
    intro *.
    by rewrite if_false.
  }.
  apply Hp.
Qed.

lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left] box_nan (t:timestamp) (i:index):
  (not (happens((MVC i)))) => happens(t) => (box(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /box; apply IH; [1:constraints | 2:auto]).
  - by rewrite /box.
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /box.
      rewrite if_false; 1: auto.
      by apply IH.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /box.  
    by apply IH. 
Qed.

lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left] box_val_mvp :
forall i,
happens(MVP) =>
 (box(i)@ pred MVP =  if happens(MVC(i)) then box(i)@MVC(i) else zero).
Proof.
intro *.
simpl.
case happens(MVC(i));intro hmvc.
  + rewrite if_true0.
    have Rw := box_geq_value (pred MVP) i.
    apply Rw; 1: auto.
    have ? // := Trace.MVC_MVP i.
  + rewrite if_false0. 
    have Rw := box_nan (pred MVP) i.
    by apply Rw.   
Qed.

  
global lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left] deduce_input_pred_MVP_box : 
Let rest = (sk_mix1,seedA_enc1,seedB_enc1,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MVP)] ->
$( (frame@pred MVP, 
  input@Avote,
  input@Bvote,
  fun i => input@MVC(i), rest) 
  |> (fun i => box i@pred MVP)).
Proof.
intro rest.
intro Hap.
have hap : happens(pred(MVP)) by constraints.
have Rewbox := (box_val_mvp).
rewrite Rewbox; 1:auto.
rewrite /box.
deduce ~all.
Qed.


lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left] bb_val (t:timestamp): 
happens(t,BBS) => ( BBS <= t) => (BB@BBS =BB@t).
Proof.
induction t; intro *.
have neq : ((pred t) < t) by auto.
have hap : happens( pred t,BBS) by auto.
have Ht := H (pred t) neq hap.  
case t; intro Eq; 
try (  rewrite -Eq;  
  rewrite /BB;
  auto).  
* auto. 
* auto.
Qed.


lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left]
count_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MOC i <= t =>
  count(i)@ t = count(i)@MOC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MOC i;intro rc.
  + rewrite rc. auto.
  + case t < MOC i; 1: constraints.
    intro Hleq.
    have Hp := H (pred t).
    rewrite !impl_true in Hp; 1,2,3: constraints.
    have -> : count(i)@t = count(i)@pred t. {
      case t; intro Ht => //.
      destruct Ht as [i0 Ceq].
      case i = i0; 1: auto.
      intro *.
      by rewrite if_false.
    }.
    apply Hp.
Qed.

lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left] count_nan (t:timestamp) (i:index):
  (not (happens((MOC i)))) => happens(t) => (count(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /count; apply IH; [1:constraints | 2:auto]).
  - by rewrite /count.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /count.  
    by apply IH. 
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /count.
      rewrite if_false; 1:apply Case.
      by apply IH.
Qed.

lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left] count_val_mop :
forall i,
happens(MOP) =>
 (count(i)@ pred MOP =  if happens(MOC(i)) then count(i)@MOC(i) else zero).
Proof.
intro *.
simpl.
case happens(MOC(i));intro hmoc.
  + rewrite if_true0.
    have Rw := count_geq_value (pred MOP) i.
    apply Rw ; 1: auto.
    have ? // := Trace.any_MOP (MOC(i)).
  + rewrite if_false0. 
    have Rw := count_nan (pred MOP) i.
    by apply Rw.   
Qed.


global lemma [Privacy_real/left, Privacy_Left_CCA_pk1/left] deduce_input_pred_MOP_count : 
Let rest = (sk_mix2,seedA_enc2,seedB_enc2,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MOP)] ->
$( (frame@pred MOP,
  fun i => input@MOC(i),
  fun i => if happens(MOC(i)) then BB@pred (MOC(i)) else witness,
  input@Avote,
  input@Bvote,
 rest) 
  |> (fun i => count i@pred MOP)).
Proof.
intro rest Hap.
have hap : happens(pred(MOP)) by constraints.
have Rewbox := count_val_mop.
rewrite Rewbox; 1:constraints.
rewrite /count.
deduce ~all.
Qed.

end SwitchLeftRealPK1.


global lemma 
[Privacy_real/left, Privacy_Left_CCA_pk1/left]  switch_Left_real_pk1 (t:_[const]):
Let rest = (sk_mix1,sk_mix2,kc0,kc1,tkA,tkB,rdAdmin,v0,v1,
            seedA_enc1,seedA_enc2,seedB_enc1,seedB_enc2) in
[happens(t,BBS)] -> equiv(frame@t,exec@t, rest).
Proof.
intro rest Hap.
induction t; try 
  (rewrite /frame /output /* //=;
  by apply IH).
(* Init *)    
- auto.
- rewrite /frame /output.
  enrich 
   BB@pred Aopening,
   frame@pred Aopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Aopening_BBS Hap).
  have rewbb : BB@pred Aopening = BB@BBS. {
    rewrite (SwitchLeftRealPK1.bb_val (pred Aopening)).
    have Rew :=  Trace.BBS_Aopening.
    constraints. constraints.
    auto.
   }
  rewrite !rewbb.   
  clear rewbb.
  rewrite /BB /bb1 /bb2.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output.
  enrich 
   BB@pred Bopening,
   frame@pred Bopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Bopening_BBS Hap).
  have rewbb : BB@pred Bopening = BB@BBS. {
  rewrite (SwitchLeftRealPK1.bb_val (pred Bopening)).
    have Rew :=  Trace.BBS_Bopening.
    constraints. constraints.
    auto.
  }
  rewrite !rewbb.   
  clear rewbb.
  rewrite /BB /bb1 /bb2.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output /exec.
  enrich fun i => box i@pred MVP, frame@pred MVP.
  deduce 2.
  have hap : happens(MVP) by constraints.
  have Ded := (SwitchLeftRealPK1.deduce_input_pred_MVP_box hap).
  deduce with Ded.
  clear Ded.
  have Ded :=  deduce_input_pred_MVP_MVC hap.
  deduce with Ded.
  clear Ded.
  clear hap.
  assert happens(MVP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded :=  deduce_input_pred_MVP_Avote hap.
  deduce with Ded.
  clear Ded. 

  clear hap.
  assert happens(MVP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded :=  deduce_input_pred_MVP_Bvote hap.
  deduce with Ded.
  clear Ded. 
  
  apply IH. 
- rewrite /frame /output /exec /cond.
  simpl ~diffr.
  enrich 
   frame@pred MOP,
   fun i => count i@pred MOP,
   input@Avote, input@Bvote,
   BB@pred MOP,
   fun i => input@MVC(i),
   fun i => input@MOC(i).
  deduce 7.
   
  have hap: happens(MOP). constraints.
  have Ded :=  (SwitchLeftRealPK1.deduce_input_pred_MOP_count hap ).
  deduce with Ded.
  clear Ded.

  have Ded := (deduce_input_pred_MOP_MOC hap).
  deduce with Ded. 
  clear Ded.
 
  have Ded := (deduce_input_pred_MOP_MVC hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded := (deduce_input_pred_MOP_Avote hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded := (deduce_input_pred_MOP_Bvote hap).
  deduce with Ded. 
  clear Ded.

  have Rewmop := SwitchLeftRealPK1.bb_val (pred MOP).
  rewrite -Rewmop; 2:constraints. {
    have h : BBS < MOP. by apply Trace.any_MOP BBS.
    constraints.
  }
  have Rewmoc : forall i, 
   if happens(MOC(i)) then BB@pred (MOC(i)) else  witness =
   if happens(MOC(i)) then BB@BBS else witness. {
   intro i.
   case happens(MOC(i)); intro Hapmoc.
   + rewrite if_true0.
     rewrite (SwitchLeftRealPK1.bb_val (pred (MOC(i)))). {
     have h : BBS < MOC(i). by apply Trace.BBS_MOC i.
     constraints.
     }
     constraints.
     auto.     
   + by rewrite !if_false0.
  }
  rewrite Rewmoc.
  deduce.

  rewrite /BB.
  rewrite /bb1 /bb2.     
  simpl ~diffr. 
  have Ded := deduce_input_pred_MOP_BBS.
  deduce with Ded; 1:constraints.
  
  apply IH.
Qed.



namespace SwitchLeftPK1PK2.

lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left]
box_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MVC i <= t =>
  box(i)@ t = box(i)@MVC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MVC i; 1: auto.
  intro Hmc.
  case t < MVC i; 1: constraints.
  intro Hleq.
  have Hp := H (pred t).
  rewrite !impl_true in Hp; 1,2,3: constraints.
  have -> : box(i)@t = box(i)@pred t. {
    case t; intro Ht => //.
    destruct Ht as [i0 Ceq].
    case i = i0; 1: auto.
    intro *.
    by rewrite if_false.
  }.
  apply Hp.
Qed.

lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left] box_nan (t:timestamp) (i:index):
  (not (happens((MVC i)))) => happens(t) => (box(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /box; apply IH; [1:constraints | 2:auto]).
  - by rewrite /box.
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /box.
      rewrite if_false; 1: auto.
      by apply IH.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /box.  
    by apply IH. 
Qed.

lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left] box_val_mvp :
forall i,
happens(MVP) =>
 (box(i)@ pred MVP =  if happens(MVC(i)) then box(i)@MVC(i) else zero).
Proof.
intro *.
simpl.
case happens(MVC(i));intro hmvc.
  + rewrite if_true0.
    have Rw := box_geq_value (pred MVP) i.
    apply Rw; 1: auto.
    have ? // := Trace.MVC_MVP i.
  + rewrite if_false0. 
    have Rw := box_nan (pred MVP) i.
    by apply Rw.   
Qed.

  
global lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left] deduce_input_pred_MVP_box : 
Let rest = (sk_mix1,seedA_enc1,seedB_enc1,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MVP)] ->
$( (frame@pred MVP, 
  input@Avote,
  input@Bvote,
  fun i => input@MVC(i), rest) 
  |> (fun i => box i@pred MVP)).
Proof.
intro rest.
intro Hap.
have hap : happens(pred(MVP)) by constraints.
have Rewbox := (box_val_mvp).
rewrite Rewbox; 1:auto.
rewrite /box.
rewrite /m8 /m4.
rewrite /ubA6 /ubB6 /cmA2 /cmB2.
rewrite /cmB4.
simpl ~diffr.
deduce ~all.
Qed.


lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left] bb_val (t:timestamp): 
happens(t,BBS) => ( BBS <= t) => (BB@BBS =BB@t).
Proof.
induction t; intro *.
have neq : ((pred t) < t) by auto.
have hap : happens( pred t,BBS) by auto.
have Ht := H (pred t) neq hap.  
case t; intro Eq; 
try (  rewrite -Eq;  
  rewrite /BB;
  auto).  
* auto. 
* auto.
Qed.


lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left]
count_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MOC i <= t =>
  count(i)@ t = count(i)@MOC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MOC i;intro rc.
  + rewrite rc. auto.
  + case t < MOC i; 1: constraints.
    intro Hleq.
    have Hp := H (pred t).
    rewrite !impl_true in Hp; 1,2,3: constraints.
    have -> : count(i)@t = count(i)@pred t. {
      case t; intro Ht => //.
      destruct Ht as [i0 Ceq].
      case i = i0; 1: auto.
      intro *.
      by rewrite if_false.
    }.
    apply Hp.
Qed.

lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left] count_nan (t:timestamp) (i:index):
  (not (happens((MOC i)))) => happens(t) => (count(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /count; apply IH; [1:constraints | 2:auto]).
  - by rewrite /count.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /count.  
    by apply IH. 
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /count.
      rewrite if_false; 1:apply Case.
      by apply IH.
Qed.

lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left] count_val_mop :
forall i,
happens(MOP) =>
 (count(i)@ pred MOP =  if happens(MOC(i)) then count(i)@MOC(i) else zero).
Proof.
intro *.
simpl.
case happens(MOC(i));intro hmoc.
  + rewrite if_true0.
    have Rw := count_geq_value (pred MOP) i.
    apply Rw ; 1: auto.
    have ? // := Trace.any_MOP (MOC(i)).
  + rewrite if_false0. 
    have Rw := count_nan (pred MOP) i.
    by apply Rw.   
Qed.


global lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left] deduce_input_pred_MOP_count : 
Let rest = (sk_mix2,seedA_enc2,seedB_enc2,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MOP,BBS) ] ->
$( (frame@pred MOP,
  fun i => input@MOC(i),
  fun i => if happens(MOC(i)) then BB@pred (MOC(i)) else witness,
  input@Avote,
  input@Bvote,
 rest) 
  |> (fun i => count i@pred MOP)).
Proof.
intro rest Hap.
have hap : happens(pred(MOP)) by constraints.
have Rewbox := count_val_mop.
rewrite Rewbox; 1:constraints.
rewrite /count.
rewrite /m5 /m9.
simpl ~diffr.
rewrite /iA3 /iA7 /iB3 /iB7.
simpl ~diffr.
have h : forall i, 
 happens(MOC(i)) => BB@pred (MOC(i)) =  BB@BBS. {
  intro i Hmc.
  have h:= bb_val (pred (MOC(i))).
  rewrite h.
  have leq := (Trace.BBS_MOC i).
  constraints.
  auto. auto.
}
rewrite !h. auto. auto.
deduce ~all.
Qed.

end SwitchLeftPK1PK2.

global lemma [Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left] 
  switch_Left_pk1_pk2 (t:_[const]):
Let rest = (sk_mix1,sk_mix2,kc0,kc1,tkA,tkB,rdAdmin,v0,v1,
            seedA_enc1,seedA_enc2,seedB_enc1,seedB_enc2) in
[happens(t,BBS)] -> equiv(frame@t,exec@t, rest).
Proof.
intro rest Hap.
induction t; try 
  (rewrite /frame /output /* //=;
  by apply IH).
(* Init *)    
- auto.
- rewrite /frame /output /exec.
  enrich 
   diff(BB@pred Aopening,BB@BBS),
   frame@pred Aopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Aopening_BBS Hap).
  have rewbb : BB@pred Aopening = BB@BBS. {
    rewrite (SwitchLeftPK1PK2.bb_val (pred Aopening)).
    have Rew :=  Trace.BBS_Aopening.
    constraints. constraints.
    auto.
   }
  rewrite !rewbb.   
  clear rewbb.
  simpl ~diffr.
  rewrite /BB /bb2 /bb4.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output.
  enrich 
   diff(BB@pred Bopening,BB@BBS),
   frame@pred Bopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Bopening_BBS Hap).
  have rewbb : BB@pred Bopening = BB@BBS. {
  rewrite (SwitchLeftPK1PK2.bb_val (pred Bopening)).
    have Rew :=  Trace.BBS_Bopening.
    constraints. constraints.
    auto.
  }
  rewrite !rewbb.   
  clear rewbb.
  rewrite /BB /bb2 /bb4.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output /exec.
  enrich fun i => box i@pred MVP, frame@pred MVP.
  deduce 2.
  have hap : happens(MVP) by constraints.
  have Ded := (SwitchLeftPK1PK2.deduce_input_pred_MVP_box hap).
  deduce with Ded.
  clear Ded.
  have Ded :=  deduce_input_pred_MVP_MVC hap.
  deduce with Ded.
  clear Ded.
  clear hap.
  assert happens(MVP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded :=  deduce_input_pred_MVP_Avote hap.
  deduce with Ded.
  clear Ded. 

  clear hap.
  assert happens(MVP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded :=  deduce_input_pred_MVP_Bvote hap.
  deduce with Ded.
  clear Ded. 
  
  apply IH. 
- rewrite /frame /output /exec /cond.
  simpl ~diffr.
  enrich 
   frame@pred MOP,
   fun i => count i@pred MOP,
   input@Avote, input@Bvote,
   diff(BB@pred MOP,BB@BBS),
   fun i => input@MVC(i),
   fun i => input@MOC(i).
 deduce 7.

   
  have hap: happens(MOP). constraints.
  have Ded :=  (SwitchLeftPK1PK2.deduce_input_pred_MOP_count Hap ).
  deduce with Ded.
  clear Ded.

  have Ded := (deduce_input_pred_MOP_MOC hap).
  deduce with Ded. 
  clear Ded.
 
  have Ded := (deduce_input_pred_MOP_MVC hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded := (deduce_input_pred_MOP_Avote hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded := (deduce_input_pred_MOP_Bvote hap).
  deduce with Ded. 
  clear Ded.

  have Rewmop := SwitchLeftPK1PK2.bb_val (pred MOP).
  rewrite -Rewmop; 2:constraints. {
    have h : BBS < MOP. by apply Trace.any_MOP BBS.
    constraints.
  }
  have Rewmoc : forall i, 
   happens(MOC(i)) =>  BB@pred (MOC(i)) = BB@BBS. {
   intro i. intro Hapmoc.
   rewrite (SwitchLeftPK1PK2.bb_val (pred (MOC(i)))). {
     have h : BBS < MOC(i). by apply Trace.BBS_MOC i.
     constraints.
     }
     constraints.
     auto.
  }
  rewrite Rewmoc; 1: auto.
  deduce.

  rewrite /BB.
  rewrite /bb2 /bb4.     
  simpl ~diffr. 
  have Ded := deduce_input_pred_MOP_BBS.
  deduce with Ded; 1:constraints.
  
  apply IH.
Qed.


namespace SwitchLeftPK2CCA.

lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left] 
box_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MVC i <= t =>
  box(i)@ t = box(i)@MVC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MVC i; 1: auto.
  intro Hmc.
  case t < MVC i; 1: constraints.
  intro Hleq.
  have Hp := H (pred t).
  rewrite !impl_true in Hp; 1,2,3: constraints.
  have -> : box(i)@t = box(i)@pred t. {
    case t; intro Ht => //.
    destruct Ht as [i0 Ceq].
    case i = i0; 1: auto.
    intro *.
    by rewrite if_false.
  }.
  apply Hp.
Qed.

lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left]  box_nan (t:timestamp) (i:index):
  (not (happens((MVC i)))) => happens(t) => (box(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /box; apply IH; [1:constraints | 2:auto]).
  - by rewrite /box.
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /box.
      rewrite if_false; 1: auto.
      by apply IH.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /box.  
    by apply IH. 
Qed.

lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left]  box_val_mvp :
forall i,
happens(MVP) =>
 (box(i)@ pred MVP =  if happens(MVC(i)) then box(i)@MVC(i) else zero).
Proof.
intro *.
simpl.
case happens(MVC(i));intro hmvc.
  + rewrite if_true0.
    have Rw := box_geq_value (pred MVP) i.
    apply Rw; 1: auto.
    have ? // := Trace.MVC_MVP i.
  + rewrite if_false0. 
    have Rw := box_nan (pred MVP) i.
    by apply Rw.   
Qed.

  
global lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left]  deduce_input_pred_MVP_box : 
Let rest = (sk_mix1,seedA_enc1,seedB_enc1,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MVP)] ->
$( (frame@pred MVP, 
  input@Avote,
  input@Bvote,
  fun i => input@MVC(i), rest) 
  |> (fun i => box i@pred MVP)).
Proof.
intro rest.
intro Hap.
have hap : happens(pred(MVP)) by constraints.
have Rewbox := (box_val_mvp).
rewrite Rewbox; 1:auto.
rewrite /box.
simpl ~diffr.
deduce ~all.
Qed.


lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left]  bb_val (t:timestamp): 
happens(t,BBS) => ( BBS <= t) => (BB@BBS =BB@t).
Proof.
induction t; intro *.
have neq : ((pred t) < t) by auto.
have hap : happens( pred t,BBS) by auto.
have Ht := H (pred t) neq hap.  
case t; intro Eq; 
try (  rewrite -Eq;  
  rewrite /BB;
  auto).  
* auto. 
* auto.
Qed.


lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left] 
count_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MOC i <= t =>
  count(i)@ t = count(i)@MOC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MOC i;intro rc.
  + rewrite rc. auto.
  + case t < MOC i; 1: constraints.
    intro Hleq.
    have Hp := H (pred t).
    rewrite !impl_true in Hp; 1,2,3: constraints.
    have -> : count(i)@t = count(i)@pred t. {
      case t; intro Ht => //.
      destruct Ht as [i0 Ceq].
      case i = i0; 1: auto.
      intro *.
      by rewrite if_false.
    }.
    apply Hp.
Qed.

lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left]  count_nan (t:timestamp) (i:index):
  (not (happens((MOC i)))) => happens(t) => (count(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /count; apply IH; [1:constraints | 2:auto]).
  - by rewrite /count.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /count.  
    by apply IH. 
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /count.
      rewrite if_false; 1:apply Case.
      by apply IH.
Qed.

lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left]  count_val_mop :
forall i,
happens(MOP) =>
 (count(i)@ pred MOP =  if happens(MOC(i)) then count(i)@MOC(i) else zero).
Proof.
intro *.
simpl.
case happens(MOC(i));intro hmoc.
  + rewrite if_true0.
    have Rw := count_geq_value (pred MOP) i.
    apply Rw ; 1: auto.
    have ? // := Trace.any_MOP (MOC(i)).
  + rewrite if_false0. 
    have Rw := count_nan (pred MOP) i.
    by apply Rw.   
Qed.


global lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left]  deduce_input_pred_MOP_count : 
Let rest = (sk_mix2,seedA_enc2,seedB_enc2,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MOP,BBS) ] ->
$( (frame@pred MOP,
  fun i => input@MOC(i),
  fun i => if happens(MOC(i)) then BB@pred (MOC(i)) else witness,
  input@Avote,
  input@Bvote,
 rest) 
  |> (fun i => count i@pred MOP)).
Proof.
intro rest Hap.
have hap : happens(pred(MOP)) by constraints.
have Rewbox := count_val_mop.
rewrite Rewbox; 1:constraints.
rewrite /count.
simpl ~diffr.
rewrite /iA /iA7 /iB /iB7.
simpl ~diffr.
have h : forall i, 
 happens(MOC(i)) => BB@pred (MOC(i)) =  BB@BBS. {
  intro i Hmc.
  have h:= bb_val (pred (MOC(i))).
  rewrite h.
  have leq := (Trace.BBS_MOC i).
  constraints. auto. auto.
}
rewrite !h. auto. auto.
deduce ~all.
Qed.

end SwitchLeftPK2CCA.

global lemma [Privacy_Left_CCA_pk2/right, Privacy_CCA/left] 
  switch_Left_pk2_cca (t:_[const]):
Let rest = (sk_mix1,sk_mix2,kc0,kc1,tkA,tkB,rdAdmin,v0,v1,
            seedA_enc1,seedA_enc2,seedB_enc1,seedB_enc2) in
[happens(t,BBS)] -> equiv(frame@t,exec@t, rest).
Proof.
intro rest Hap.
induction t; try 
  (rewrite /frame /output /* //=;
  by apply IH).
(* Init *)    
- auto.
- rewrite /frame /output /exec.
  enrich 
   diff(BB@BBS,BB@pred Aopening),
   frame@pred Aopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Aopening_BBS Hap).
  have rewbb : BB@pred Aopening = BB@BBS. {
    rewrite (SwitchLeftPK2CCA.bb_val (pred Aopening)).
    have Rew :=  Trace.BBS_Aopening.
    constraints. constraints.
    auto.
   }
  rewrite !rewbb.   
  clear rewbb.
  simpl ~diffr.
  rewrite /BB /bb4 /bb.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output.
  enrich 
   diff(BB@BBS,BB@pred Bopening),
   frame@pred Bopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Bopening_BBS Hap).
  have rewbb : BB@pred Bopening = BB@BBS. {
  rewrite (SwitchLeftPK2CCA.bb_val (pred Bopening)).
    have Rew :=  Trace.BBS_Bopening.
    constraints. constraints.
    auto.
  }
  rewrite !rewbb.   
  clear rewbb.
  rewrite /BB /bb /bb4.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output /exec.
  enrich fun i => box i@pred MVP, frame@pred MVP.
  deduce 2.
  have hap : happens(MVP) by constraints.
  have Ded := (SwitchLeftPK2CCA.deduce_input_pred_MVP_box hap).
  deduce with Ded.
  clear Ded.
  have Ded :=  deduce_input_pred_MVP_MVC hap.
  deduce with Ded.
  clear Ded.
  clear hap.
  assert happens(MVP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded :=  deduce_input_pred_MVP_Avote hap.
  deduce with Ded.
  clear Ded. 

  clear hap.
  assert happens(MVP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded :=  deduce_input_pred_MVP_Bvote hap.
  deduce with Ded.
  clear Ded. 
  
  apply IH. 
- rewrite /frame /output /exec /cond.
  simpl ~diffr.
  enrich 
   frame@pred MOP,
   fun i => count i@pred MOP,
   input@Avote, input@Bvote,
   diff(BB@BBS,BB@pred MOP),
   fun i => input@MVC(i),
   fun i => input@MOC(i).
 deduce 7.

   
  have hap: happens(MOP). constraints.
  have Ded :=  (SwitchLeftPK2CCA.deduce_input_pred_MOP_count Hap ).
  deduce with Ded.
  clear Ded.

  have Ded := (deduce_input_pred_MOP_MOC hap).
  deduce with Ded. 
  clear Ded.
 
  have Ded := (deduce_input_pred_MOP_MVC hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded := (deduce_input_pred_MOP_Avote hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded := (deduce_input_pred_MOP_Bvote hap).
  deduce with Ded. 
  clear Ded.

  have Rewmop := SwitchLeftPK2CCA.bb_val (pred MOP).
  rewrite -Rewmop; 2:constraints. {
    have h : BBS < MOP. by apply Trace.any_MOP BBS.
    constraints.
  }
  have Rewmoc : forall i, 
   happens(MOC(i)) =>  BB@pred (MOC(i)) = BB@BBS. {
   intro i. intro Hapmoc.
   rewrite (SwitchLeftPK2CCA.bb_val (pred (MOC(i)))). {
     have h : BBS < MOC(i). by apply Trace.BBS_MOC i.
     constraints.
     }
     constraints.
     auto.
  }
  rewrite Rewmoc; 1: auto.
  deduce.

  rewrite /BB.
  rewrite /bb /bb4.     
  simpl ~diffr. 
  have Ded := deduce_input_pred_MOP_BBS.
  deduce with Ded; 1:constraints.
  
  apply IH.
Qed.



 
global lemma [Privacy_real/left,Privacy_CCA/left] rewrite_cca_left (t:_[const]) : [happens(t,BBS)]
-> equiv(frame@t).
Proof.
intro Hap.
trans [Privacy_Left_CCA_pk1].
* trans [set:Privacy_real/left, Privacy_Left_CCA_pk1/left;
       equiv:(Privacy_real/left, Privacy_Left_CCA_pk1/left)]; 
     1,3 : refl.
   - by apply switch_Left_real_pk1.
* by apply Left_CCA_pk1.
* trans [Privacy_Left_CCA_pk2].   
    - trans [set:Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left;
       equiv:(Privacy_Left_CCA_pk1/right, Privacy_Left_CCA_pk2/left)]; 
     1,3 : refl.
      ** by apply switch_Left_pk1_pk2.
    - by apply Left_CCA_pk2. 
    - trans [set:Privacy_Left_CCA_pk2/right, Privacy_CCA/left;
       equiv:(Privacy_Left_CCA_pk2/right, Privacy_CCA/left)]; 
     1,3 : refl.
     ** by apply switch_Left_pk2_cca.
Qed.



(* same for Right, copy past and change names when stable*)



namespace SwitchRightRealPK1.

lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left]
box_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MVC i <= t =>
  box(i)@ t = box(i)@MVC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MVC i; 1: auto.
  intro Hmc.
  case t < MVC i; 1: constraints.
  intro Hleq.
  have Hp := H (pred t).
  rewrite !impl_true in Hp; 1,2,3: constraints.
  have -> : box(i)@t = box(i)@pred t. {
    case t; intro Ht => //.
    destruct Ht as [i0 Ceq].
    case i = i0; 1: auto.
    intro *.
    by rewrite if_false.
  }.
  apply Hp.
Qed.

lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left] box_nan (t:timestamp) (i:index):
  (not (happens((MVC i)))) => happens(t) => (box(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /box; apply IH; [1:constraints | 2:auto]).
  - by rewrite /box.
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /box.
      rewrite if_false; 1: auto.
      by apply IH.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /box.  
    by apply IH. 
Qed.

lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left] box_val_mvp :
forall i,
happens(MVP) =>
 (box(i)@ pred MVP =  if happens(MVC(i)) then box(i)@MVC(i) else zero).
Proof.
intro *.
simpl.
case happens(MVC(i));intro hmvc.
  + rewrite if_true0.
    have Rw := box_geq_value (pred MVP) i.
    apply Rw; 1: auto.
    have ? // := Trace.MVC_MVP i.
  + rewrite if_false0. 
    have Rw := box_nan (pred MVP) i.
    by apply Rw.   
Qed.

  
global lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left] deduce_input_pred_MVP_box : 
Let rest = (sk_mix1,seedA_enc1,seedB_enc1,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MVP)] ->
$( (frame@pred MVP, 
  input@Avote,
  input@Bvote,
  fun i => input@MVC(i), rest) 
  |> (fun i => box i@pred MVP)).
Proof.
intro rest.
intro Hap.
have hap : happens(pred(MVP)) by constraints.
have Rewbox := (box_val_mvp).
rewrite Rewbox; 1:auto.
rewrite /box.
deduce ~all.
Qed.


lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left] bb_val (t:timestamp): 
happens(t,BBS) => ( BBS <= t) => (BB@BBS =BB@t).
Proof.
induction t; intro *.
have neq : ((pred t) < t) by auto.
have hap : happens( pred t,BBS) by auto.
have Ht := H (pred t) neq hap.  
case t; intro Eq; 
try (  rewrite -Eq;  
  rewrite /BB;
  auto).  
* auto. 
* auto.
Qed.


lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left]
count_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MOC i <= t =>
  count(i)@ t = count(i)@MOC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MOC i;intro rc.
  + rewrite rc. auto.
  + case t < MOC i; 1: constraints.
    intro Hleq.
    have Hp := H (pred t).
    rewrite !impl_true in Hp; 1,2,3: constraints.
    have -> : count(i)@t = count(i)@pred t. {
      case t; intro Ht => //.
      destruct Ht as [i0 Ceq].
      case i = i0; 1: auto.
      intro *.
      by rewrite if_false.
    }.
    apply Hp.
Qed.

lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left] count_nan (t:timestamp) (i:index):
  (not (happens((MOC i)))) => happens(t) => (count(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /count; apply IH; [1:constraints | 2:auto]).
  - by rewrite /count.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /count.  
    by apply IH. 
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /count.
      rewrite if_false; 1:apply Case.
      by apply IH.
Qed.

lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left] count_val_mop :
forall i,
happens(MOP) =>
 (count(i)@ pred MOP =  if happens(MOC(i)) then count(i)@MOC(i) else zero).
Proof.
intro *.
simpl.
case happens(MOC(i));intro hmoc.
  + rewrite if_true0.
    have Rw := count_geq_value (pred MOP) i.
    apply Rw ; 1: auto.
    have ? // := Trace.any_MOP (MOC(i)).
  + rewrite if_false0. 
    have Rw := count_nan (pred MOP) i.
    by apply Rw.   
Qed.


global lemma [Privacy_real/right, Privacy_Right_CCA_pk1/left] deduce_input_pred_MOP_count : 
Let rest = (sk_mix2,seedA_enc2,seedB_enc2,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MOP)] ->
$( (frame@pred MOP,
  fun i => input@MOC(i),
  fun i => if happens(MOC(i)) then BB@pred (MOC(i)) else witness,
  input@Avote,
  input@Bvote,
 rest) 
  |> (fun i => count i@pred MOP)).
Proof.
intro rest Hap.
have hap : happens(pred(MOP)) by constraints.
have Rewbox := count_val_mop.
rewrite Rewbox; 1:constraints.
rewrite /count.
deduce ~all.
Qed.

end SwitchRightRealPK1.


global lemma 
[Privacy_real/right, Privacy_Right_CCA_pk1/left]  switch_Right_real_pk1 (t:_[const]):
Let rest = (sk_mix1,sk_mix2,kc0,kc1,tkA,tkB,rdAdmin,v0,v1,
            seedA_enc1,seedA_enc2,seedB_enc1,seedB_enc2) in
[happens(t,BBS)] -> equiv(frame@t,exec@t, rest).
Proof.
intro rest Hap.
induction t; try 
  (rewrite /frame /output /* //=;
  by apply IH).
(* Init *)    
- auto.
- rewrite /frame /output.
  enrich 
   BB@pred Aopening,
   frame@pred Aopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Aopening_BBS Hap).
  have rewbb : BB@pred Aopening = BB@BBS. {
    rewrite (SwitchRightRealPK1.bb_val (pred Aopening)).
    have Rew :=  Trace.BBS_Aopening.
    constraints. constraints.
    auto.
   }
  rewrite !rewbb.   
  clear rewbb.
  rewrite /BB /bb1 /bb3.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output.
  enrich 
   BB@pred Bopening,
   frame@pred Bopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Bopening_BBS Hap).
  have rewbb : BB@pred Bopening = BB@BBS. {
  rewrite (SwitchRightRealPK1.bb_val (pred Bopening)).
    have Rew :=  Trace.BBS_Bopening.
    constraints. constraints.
    auto.
  }
  rewrite !rewbb.   
  clear rewbb.
  rewrite /BB /bb1 /bb3.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output /exec.
  enrich fun i => box i@pred MVP, frame@pred MVP.
  deduce 2.
  have hap : happens(MVP) by constraints.
  have Ded := (SwitchRightRealPK1.deduce_input_pred_MVP_box hap).
  deduce with Ded.
  clear Ded.
  have Ded :=  deduce_input_pred_MVP_MVC hap.
  deduce with Ded.
  clear Ded.
  clear hap.
  assert happens(MVP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded :=  deduce_input_pred_MVP_Avote hap.
  deduce with Ded.
  clear Ded. 

  clear hap.
  assert happens(MVP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded :=  deduce_input_pred_MVP_Bvote hap.
  deduce with Ded.
  clear Ded. 
  
  apply IH. 
- rewrite /frame /output /exec /cond.
  simpl ~diffr.
  enrich 
   frame@pred MOP,
   fun i => count i@pred MOP,
   input@Avote, input@Bvote,
   BB@pred MOP,
   fun i => input@MVC(i),
   fun i => input@MOC(i).
  deduce 7.
   
  have hap: happens(MOP). constraints.
  have Ded :=  (SwitchRightRealPK1.deduce_input_pred_MOP_count hap ).
  deduce with Ded.
  clear Ded.

  have Ded := (deduce_input_pred_MOP_MOC hap).
  deduce with Ded. 
  clear Ded.
 
  have Ded := (deduce_input_pred_MOP_MVC hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded := (deduce_input_pred_MOP_Avote hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded := (deduce_input_pred_MOP_Bvote hap).
  deduce with Ded. 
  clear Ded.

  have Rewmop := SwitchRightRealPK1.bb_val (pred MOP).
  rewrite -Rewmop; 2:constraints. {
    have h : BBS < MOP. by apply Trace.any_MOP BBS.
    constraints.
  }
  have Rewmoc : forall i, 
   if happens(MOC(i)) then BB@pred (MOC(i)) else  witness =
   if happens(MOC(i)) then BB@BBS else witness. {
   intro i.
   case happens(MOC(i)); intro Hapmoc.
   + rewrite if_true0.
     rewrite (SwitchRightRealPK1.bb_val (pred (MOC(i)))). {
     have h : BBS < MOC(i). by apply Trace.BBS_MOC i.
     constraints.
     }
     constraints.
     auto.     
   + by rewrite !if_false0.
  }
  rewrite Rewmoc.
  deduce.

  rewrite /BB.
  rewrite /bb1 /bb3.     
  simpl ~diffr. 
  have Ded := deduce_input_pred_MOP_BBS.
  deduce with Ded; 1:constraints.
  
  apply IH.
Qed.



namespace SwitchRightPK1PK2.

lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left]
box_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MVC i <= t =>
  box(i)@ t = box(i)@MVC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MVC i; 1: auto.
  intro Hmc.
  case t < MVC i; 1: constraints.
  intro Hleq.
  have Hp := H (pred t).
  rewrite !impl_true in Hp; 1,2,3: constraints.
  have -> : box(i)@t = box(i)@pred t. {
    case t; intro Ht => //.
    destruct Ht as [i0 Ceq].
    case i = i0; 1: auto.
    intro *.
    by rewrite if_false.
  }.
  apply Hp.
Qed.

lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left] box_nan (t:timestamp) (i:index):
  (not (happens((MVC i)))) => happens(t) => (box(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /box; apply IH; [1:constraints | 2:auto]).
  - by rewrite /box.
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /box.
      rewrite if_false; 1: auto.
      by apply IH.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /box.  
    by apply IH. 
Qed.

lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left] box_val_mvp :
forall i,
happens(MVP) =>
 (box(i)@ pred MVP =  if happens(MVC(i)) then box(i)@MVC(i) else zero).
Proof.
intro *.
simpl.
case happens(MVC(i));intro hmvc.
  + rewrite if_true0.
    have Rw := box_geq_value (pred MVP) i.
    apply Rw; 1: auto.
    have ? // := Trace.MVC_MVP i.
  + rewrite if_false0. 
    have Rw := box_nan (pred MVP) i.
    by apply Rw.   
Qed.

  
global lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left] deduce_input_pred_MVP_box : 
Let rest = (sk_mix1,seedA_enc1,seedB_enc1,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MVP)] ->
$( (frame@pred MVP, 
  input@Avote,
  input@Bvote,
  fun i => input@MVC(i), rest) 
  |> (fun i => box i@pred MVP)).
Proof.
intro rest.
intro Hap.
have hap : happens(pred(MVP)) by constraints.
have Rewbox := (box_val_mvp).
rewrite Rewbox; 1:auto.
rewrite /box.
simpl ~diffr.
deduce ~all.
Qed.


lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left] bb_val (t:timestamp): 
happens(t,BBS) => ( BBS <= t) => (BB@BBS =BB@t).
Proof.
induction t; intro *.
have neq : ((pred t) < t) by auto.
have hap : happens( pred t,BBS) by auto.
have Ht := H (pred t) neq hap.  
case t; intro Eq; 
try (  rewrite -Eq;  
  rewrite /BB;
  auto).  
* auto. 
* auto.
Qed.


lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left]
count_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MOC i <= t =>
  count(i)@ t = count(i)@MOC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MOC i;intro rc.
  + rewrite rc. auto.
  + case t < MOC i; 1: constraints.
    intro Hleq.
    have Hp := H (pred t).
    rewrite !impl_true in Hp; 1,2,3: constraints.
    have -> : count(i)@t = count(i)@pred t. {
      case t; intro Ht => //.
      destruct Ht as [i0 Ceq].
      case i = i0; 1: auto.
      intro *.
      by rewrite if_false.
    }.
    apply Hp.
Qed.

lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left] count_nan (t:timestamp) (i:index):
  (not (happens((MOC i)))) => happens(t) => (count(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /count; apply IH; [1:constraints | 2:auto]).
  - by rewrite /count.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /count.  
    by apply IH. 
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /count.
      rewrite if_false; 1:apply Case.
      by apply IH.
Qed.

lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left] count_val_mop :
forall i,
happens(MOP) =>
 (count(i)@ pred MOP =  if happens(MOC(i)) then count(i)@MOC(i) else zero).
Proof.
intro *.
simpl.
case happens(MOC(i));intro hmoc.
  + rewrite if_true0.
    have Rw := count_geq_value (pred MOP) i.
    apply Rw ; 1: auto.
    have ? // := Trace.any_MOP (MOC(i)).
  + rewrite if_false0. 
    have Rw := count_nan (pred MOP) i.
    by apply Rw.   
Qed.


global lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left] deduce_input_pred_MOP_count : 
Let rest = (sk_mix2,seedA_enc2,seedB_enc2,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MOP,BBS) ] ->
$( (frame@pred MOP,
  fun i => input@MOC(i),
  fun i => if happens(MOC(i)) then BB@pred (MOC(i)) else witness,
  input@Avote,
  input@Bvote,
 rest) 
  |> (fun i => count i@pred MOP)).
Proof.
intro rest Hap.
have hap : happens(pred(MOP)) by constraints.
have Rewbox := count_val_mop.
rewrite Rewbox; 1:constraints.
rewrite /count.
rewrite /m7 /m11.
simpl ~diffr.
rewrite /iA5 /iA9 /iB5 /iB9.
simpl ~diffr.
have h : forall i, 
 happens(MOC(i)) => BB@pred (MOC(i)) =  BB@BBS. {
  intro i Hmc.
  have h:= bb_val (pred (MOC(i))).
  rewrite h.
  have leq := (Trace.BBS_MOC i).
  constraints.
  auto. auto.
}
rewrite !h. auto. auto.
deduce ~all.
Qed.

end SwitchRightPK1PK2.

global lemma [Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left]
  switch_Right_pk1_pk2 (t:_[const]):
Let rest = (sk_mix1,sk_mix2,kc0,kc1,tkA,tkB,rdAdmin,v0,v1,
            seedA_enc1,seedA_enc2,seedB_enc1,seedB_enc2) in
[happens(t,BBS)] -> equiv(frame@t,exec@t, rest).
Proof.
intro rest Hap.
induction t; try 
  (rewrite /frame /output /* //=;
  by apply IH).
(* Init *)    
- auto.
- rewrite /frame /output /exec.
  enrich 
   diff(BB@pred Aopening,BB@BBS),
   frame@pred Aopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Aopening_BBS Hap).
  have rewbb : BB@pred Aopening = BB@BBS. {
    rewrite (SwitchRightPK1PK2.bb_val (pred Aopening)).
    have Rew :=  Trace.BBS_Aopening.
    constraints. constraints.
    auto.
   }
  rewrite !rewbb.   
  clear rewbb.
  simpl ~diffr.
  rewrite /BB /bb3 /bb5.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output.
  enrich 
   diff(BB@pred Bopening,BB@BBS),
   frame@pred Bopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Bopening_BBS Hap).
  have rewbb : BB@pred Bopening = BB@BBS. {
  rewrite (SwitchRightPK1PK2.bb_val (pred Bopening)).
    have Rew :=  Trace.BBS_Bopening.
    constraints. constraints.
    auto.
  }
  rewrite !rewbb.   
  clear rewbb.
  rewrite /BB /bb3 /bb5.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output /exec.
  enrich fun i => box i@pred MVP, frame@pred MVP.
  deduce 2.
  have hap : happens(MVP) by constraints.
  have Ded := (SwitchRightPK1PK2.deduce_input_pred_MVP_box hap).
  deduce with Ded.
  clear Ded.
  have Ded :=  deduce_input_pred_MVP_MVC hap.
  deduce with Ded.
  clear Ded.
  clear hap.
  assert happens(MVP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded :=  deduce_input_pred_MVP_Avote hap.
  deduce with Ded.
  clear Ded. 

  clear hap.
  assert happens(MVP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded :=  deduce_input_pred_MVP_Bvote hap.
  deduce with Ded.
  clear Ded. 
  
  apply IH. 
- rewrite /frame /output /exec /cond.
  simpl ~diffr.
  enrich 
   frame@pred MOP,
   fun i => count i@pred MOP,
   input@Avote, input@Bvote,
   diff(BB@pred MOP,BB@BBS),
   fun i => input@MVC(i),
   fun i => input@MOC(i).
 deduce 7.

   
  have hap: happens(MOP). constraints.
  have Ded :=  (SwitchRightPK1PK2.deduce_input_pred_MOP_count Hap ).
  deduce with Ded.
  clear Ded.

  have Ded := (deduce_input_pred_MOP_MOC hap).
  deduce with Ded. 
  clear Ded.
 
  have Ded := (deduce_input_pred_MOP_MVC hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded := (deduce_input_pred_MOP_Avote hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded := (deduce_input_pred_MOP_Bvote hap).
  deduce with Ded. 
  clear Ded.

  have Rewmop := SwitchRightPK1PK2.bb_val (pred MOP).
  rewrite -Rewmop; 2:constraints. {
    have h : BBS < MOP. by apply Trace.any_MOP BBS.
    constraints.
  }
  have Rewmoc : forall i, 
   happens(MOC(i)) =>  BB@pred (MOC(i)) = BB@BBS. {
   intro i. intro Hapmoc.
   rewrite (SwitchRightPK1PK2.bb_val (pred (MOC(i)))). {
     have h : BBS < MOC(i). by apply Trace.BBS_MOC i.
     constraints.
     }
     constraints.
     auto.
  }
  rewrite Rewmoc; 1: auto.
  deduce.

  rewrite /BB.
  rewrite /bb3 /bb5.     
  simpl ~diffr. 
  have Ded := deduce_input_pred_MOP_BBS.
  deduce with Ded; 1:constraints.
  
  apply IH.
Qed.


namespace SwitchRightPK2CCA.

lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right] 
box_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MVC i <= t =>
  box(i)@ t = box(i)@MVC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MVC i; 1: auto.
  intro Hmc.
  case t < MVC i; 1: constraints.
  intro Hleq.
  have Hp := H (pred t).
  rewrite !impl_true in Hp; 1,2,3: constraints.
  have -> : box(i)@t = box(i)@pred t. {
    case t; intro Ht => //.
    destruct Ht as [i0 Ceq].
    case i = i0; 1: auto.
    intro *.
    by rewrite if_false.
  }.
  apply Hp.
Qed.

lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right]   box_nan (t:timestamp) (i:index):
  (not (happens((MVC i)))) => happens(t) => (box(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /box; apply IH; [1:constraints | 2:auto]).
  - by rewrite /box.
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /box.
      rewrite if_false; 1: auto.
      by apply IH.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /box.  
    by apply IH. 
Qed.

lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right]   box_val_mvp :
forall i,
happens(MVP) =>
 (box(i)@ pred MVP =  if happens(MVC(i)) then box(i)@MVC(i) else zero).
Proof.
intro *.
simpl.
case happens(MVC(i));intro hmvc.
  + rewrite if_true0.
    have Rw := box_geq_value (pred MVP) i.
    apply Rw; 1: auto.
    have ? // := Trace.MVC_MVP i.
  + rewrite if_false0. 
    have Rw := box_nan (pred MVP) i.
    by apply Rw.   
Qed.

  
global lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right]   deduce_input_pred_MVP_box : 
Let rest = (sk_mix1,seedA_enc1,seedB_enc1,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MVP)] ->
$( (frame@pred MVP, 
  input@Avote,
  input@Bvote,
  fun i => input@MVC(i), rest) 
  |> (fun i => box i@pred MVP)).
Proof.
intro rest.
intro Hap.
have hap : happens(pred(MVP)) by constraints.
have Rewbox := (box_val_mvp).
rewrite Rewbox; 1:auto.
rewrite /box.
simpl ~diffr.
deduce ~all.
Qed.


lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right] bb_val (t:timestamp): 
happens(t,BBS) => ( BBS <= t) => (BB@BBS =BB@t).
Proof.
induction t; intro *.
have neq : ((pred t) < t) by auto.
have hap : happens( pred t,BBS) by auto.
have Ht := H (pred t) neq hap.  
case t; intro Eq; 
try (  rewrite -Eq;  
  rewrite /BB;
  auto).  
* auto. 
* auto.
Qed.


lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right] 
count_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MOC i <= t =>
  count(i)@ t = count(i)@MOC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MOC i;intro rc.
  + rewrite rc. auto.
  + case t < MOC i; 1: constraints.
    intro Hleq.
    have Hp := H (pred t).
    rewrite !impl_true in Hp; 1,2,3: constraints.
    have -> : count(i)@t = count(i)@pred t. {
      case t; intro Ht => //.
      destruct Ht as [i0 Ceq].
      case i = i0; 1: auto.
      intro *.
      by rewrite if_false.
    }.
    apply Hp.
Qed.

lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right] count_nan (t:timestamp) (i:index):
  (not (happens((MOC i)))) => happens(t) => (count(i)@t = zero).
Proof.
  intro Hap.
  induction t => t; case t => Ht IH Hapt;
  try (rewrite /count; apply IH; [1:constraints | 2:auto]).
  - by rewrite /count.
  - destruct Ht as [i0 Ht].
    rewrite Ht.
    rewrite /count.  
    by apply IH. 
  - destruct Ht as [i0 Ht].
    rewrite Ht in * => {Ht}.
    case i = i0; intro Case.
    * rewrite Case in Hap; constraints. 
    * rewrite /count.
      rewrite if_false; 1:apply Case.
      by apply IH.
Qed.

lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right] count_val_mop :
forall i,
happens(MOP) =>
 (count(i)@ pred MOP =  if happens(MOC(i)) then count(i)@MOC(i) else zero).
Proof.
intro *.
simpl.
case happens(MOC(i));intro hmoc.
  + rewrite if_true0.
    have Rw := count_geq_value (pred MOP) i.
    apply Rw ; 1: auto.
    have ? // := Trace.any_MOP (MOC(i)).
  + rewrite if_false0. 
    have Rw := count_nan (pred MOP) i.
    by apply Rw.   
Qed.


global lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right] deduce_input_pred_MOP_count : 
Let rest = (sk_mix2,seedA_enc2,seedB_enc2,rdAdmin,
            kc0,kc1,tkA,tkB,v0,v1)
in
[happens(MOP,BBS) ] ->
$( (frame@pred MOP,
  fun i => input@MOC(i),
  fun i => if happens(MOC(i)) then BB@pred (MOC(i)) else witness,
  input@Avote,
  input@Bvote,
 rest) 
  |> (fun i => count i@pred MOP)).
Proof.
intro rest Hap.
have hap : happens(pred(MOP)) by constraints.
have Rewbox := count_val_mop.
rewrite Rewbox; 1:constraints.
rewrite /count.
simpl ~diffr.
rewrite /iA /iA9 /iB /iB9.
simpl ~diffr.
have h : forall i, 
 happens(MOC(i)) => BB@pred (MOC(i)) =  BB@BBS. {
  intro i Hmc.
  have h:= bb_val (pred (MOC(i))).
  rewrite h.
  have leq := (Trace.BBS_MOC i).
  constraints. auto. auto.
}
rewrite !h. auto. auto.
deduce ~all.
Qed.

end SwitchRightPK2CCA.

global lemma [Privacy_Right_CCA_pk2/right, Privacy_CCA/right] 
  switch_Right_pk2_cca (t:_[const]):
Let rest = (sk_mix1,sk_mix2,kc0,kc1,tkA,tkB,rdAdmin,v0,v1,
            seedA_enc1,seedA_enc2,seedB_enc1,seedB_enc2) in
[happens(t,BBS)] -> equiv(frame@t,exec@t, rest).
Proof.
intro rest Hap.
induction t; try 
  (rewrite /frame /output /* //=;
  by apply IH).
(* Init *)    
- auto.
- rewrite /frame /output /exec.
  enrich 
   diff(BB@BBS,BB@pred Aopening),
   frame@pred Aopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Aopening_BBS Hap).
  have rewbb : BB@pred Aopening = BB@BBS. {
    rewrite (SwitchRightPK2CCA.bb_val (pred Aopening)).
    have Rew :=  Trace.BBS_Aopening.
    constraints. constraints.
    auto.
   }
  rewrite !rewbb.   
  clear rewbb.
  simpl ~diffr.
  rewrite /BB /bb5 /bb.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output.
  enrich 
   diff(BB@BBS,BB@pred Bopening),
   frame@pred Bopening.
  deduce 2.
  have DedBBS := (deduce_input_pred_Bopening_BBS Hap).
  have rewbb : BB@pred Bopening = BB@BBS. {
  rewrite (SwitchRightPK2CCA.bb_val (pred Bopening)).
    have Rew :=  Trace.BBS_Bopening.
    constraints. constraints.
    auto.
  }
  rewrite !rewbb.   
  clear rewbb.
  rewrite /BB /bb /bb5.
  simpl ~diffr.
  deduce with DedBBS.
  apply IH.
- rewrite /frame /output /exec.
  enrich fun i => box i@pred MVP, frame@pred MVP.
  deduce 2.
  have hap : happens(MVP) by constraints.
  have Ded := (SwitchRightPK2CCA.deduce_input_pred_MVP_box hap).
  deduce with Ded.
  clear Ded.
  have Ded :=  deduce_input_pred_MVP_MVC hap.
  deduce with Ded.
  clear Ded.
  clear hap.
  assert happens(MVP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded :=  deduce_input_pred_MVP_Avote hap.
  deduce with Ded.
  clear Ded. 

  clear hap.
  assert happens(MVP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded :=  deduce_input_pred_MVP_Bvote hap.
  deduce with Ded.
  clear Ded. 
  
  apply IH. 
- rewrite /frame /output /exec /cond.
  simpl ~diffr.
  enrich 
   frame@pred MOP,
   fun i => count i@pred MOP,
   input@Avote, input@Bvote,
   diff(BB@BBS,BB@pred MOP),
   fun i => input@MVC(i),
   fun i => input@MOC(i).
 deduce 7.

   
  have hap: happens(MOP). constraints.
  have Ded :=  (SwitchRightPK2CCA.deduce_input_pred_MOP_count Hap ).
  deduce with Ded.
  clear Ded.

  have Ded := (deduce_input_pred_MOP_MOC hap).
  deduce with Ded. 
  clear Ded.
 
  have Ded := (deduce_input_pred_MOP_MVC hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Avote) as hap.
  split; 1:constraints.  by apply Trace.happens_Avote.
  have Ded := (deduce_input_pred_MOP_Avote hap).
  deduce with Ded. 
  clear Ded.

  clear hap.
  assert happens(MOP,Bvote) as hap.
  split; 1:constraints.  by apply Trace.happens_Bvote.
  have Ded := (deduce_input_pred_MOP_Bvote hap).
  deduce with Ded. 
  clear Ded.

  have Rewmop := SwitchRightPK2CCA.bb_val (pred MOP).
  rewrite -Rewmop; 2:constraints. {
    have h : BBS < MOP. by apply Trace.any_MOP BBS.
    constraints.
  }
  have Rewmoc : forall i, 
   happens(MOC(i)) =>  BB@pred (MOC(i)) = BB@BBS. {
   intro i. intro Hapmoc.
   rewrite (SwitchRightPK2CCA.bb_val (pred (MOC(i)))). {
     have h : BBS < MOC(i). by apply Trace.BBS_MOC i.
     constraints.
     }
     constraints.
     auto.
  }
  rewrite Rewmoc; 1: auto.
  deduce.

  rewrite /BB.
  rewrite /bb /bb5.     
  simpl ~diffr. 
  have Ded := deduce_input_pred_MOP_BBS.
  deduce with Ded; 1:constraints.
  
  apply IH.
Qed.



 
global lemma [Privacy_real/right,Privacy_CCA/right] rewrite_cca_right (t:_[const]) : [happens(t,BBS)]
-> equiv(frame@t).
Proof.
intro Hap.
trans [Privacy_Right_CCA_pk1].
* trans [set:Privacy_real/right, Privacy_Right_CCA_pk1/left;
       equiv:(Privacy_real/right, Privacy_Right_CCA_pk1/left)]; 
     1,3 : refl.
   - by apply switch_Right_real_pk1.
* by apply Right_CCA_pk1.
* trans [Privacy_Right_CCA_pk2].   
    - trans [set:Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left;
       equiv:(Privacy_Right_CCA_pk1/right, Privacy_Right_CCA_pk2/left)]; 
     1,3 : refl.
      ** by apply switch_Right_pk1_pk2.
    - by apply Right_CCA_pk2. 
    - trans [set:Privacy_Right_CCA_pk2/right, Privacy_CCA/right;
       equiv:(Privacy_Right_CCA_pk2/right, Privacy_CCA/right)]; 
     1,3 : refl.
     ** by apply switch_Right_pk2_cca.
Qed.
