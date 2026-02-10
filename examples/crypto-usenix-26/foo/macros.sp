include[admit] processes.


namespace Macro.

(*********************************************
Lemmas to rewrite input and frame in all cases
**********************************************)

axiom [any] frame_empty (t:_[const]):
not (happens(t)) => frame@t = empty.

axiom [any] input_empty (t:_[const]):
not (happens(t)) => input@t = empty.

lemma [any] rw_frame (t:_[const]):
frame@t = if happens(t) then frame@t else empty.
Proof.
case happens(t).
* by rewrite if_true.
* rewrite if_false0.
  by rewrite frame_empty.
Qed.

lemma [any] rw_input (t:_[const]):
input@t = if happens(t) then input@t else empty.
Proof.
case happens(t).
* by rewrite if_true.
* rewrite if_false0.
  by rewrite input_empty.
Qed.


lemma [any] rw_cond_frame (t:_[const]) (b:bool):
(happens(t) =>  b) =>
frame@t = if happens(t)&&b then frame@t else empty.
Proof.
case happens(t).
* by rewrite if_true.
* rewrite if_false. auto.
  by rewrite frame_empty.
Qed.

lemma [any] rw_cond_input (t:_[const]) (b:bool):
(happens(t) =>  b) =>
input@t = if happens(t)&&b then input@t else empty.
Proof.
case happens(t).
* by rewrite if_true.
* rewrite if_false. auto.
  by rewrite input_empty.
Qed.


lemma [any/Privacy_real] rw_cond_input_moc (b:index -> bool):
forall i, ((happens(MOC(i)) => b i) => 
 input@MOC(i) = if happens(MOC(i)) && (b i) then input@MOC(i) else empty).
Proof.
intro i.
intro H.
by rewrite (rw_cond_input (MOC(i)) (b i)).
Qed.

lemma [any/Privacy_real] rw_cond_input_mvc (b:index -> bool):
forall i, ((happens(MVC(i)) => b i) => 
 input@MVC(i) = if happens(MVC(i)) && (b i) then input@MVC(i) else empty).
Proof.
intro i.
intro H.
by rewrite (rw_cond_input (MVC(i)) (b i)).
Qed.

(*******************************************************************************
## Lemmas to track values of mutable variables box
********************************************************************************)

axiom [any/Privacy_real] box_empty (t:timestamp[const]) (i:index):
not (happens(t)) => box i@t = empty.

lemma [any/Privacy_real] rw_box (t:timestamp[const]) (i:index):
box(i)@t = if happens(t) then box(i)@t else empty.
Proof.
case happens(t); intro H. 
* by rewrite if_true0. 
* rewrite if_false0.
  by rewrite box_empty.
Qed.

lemma [any/Privacy_real] rw_cond_box 
  (t:timestamp[const]) (b : index -> bool) :
forall (i:index), (
(happens(t) => b i) => 
(box(i)@t) = if happens(t) && (b i) then (box(i)@t) else empty).
Proof.
intro i H.
rewrite rw_box.
case happens(t); intro Hc. 
* rewrite if_true0.
  by rewrite if_true. 
* rewrite if_false0.
  by rewrite if_false.
Qed.

lemma [Privacy_CCA] box_nan (t:timestamp) (i:index):
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

lemma [Privacy_CCA] box_lt_value (t:timestamp[const]) (i:index) :
  happens(t,MVC i) =>  t < MVC i  => box(i)@t = zero.
Proof.
  induction t.
  intro *.
  destruct H0 as [Hc Ht].
  case t; intro Hind => //;
  try (
    have Hp := H (pred(t));
    rewrite !impl_true in Hp => //
  ).
  destruct Hind as [i0 Ceq].
  rewrite Ceq.
  case i = i0 ; intro Heq.
  - by rewrite Ceq Heq in Clt.
  - rewrite /box.
    rewrite if_false => //. 
Qed.

lemma [Privacy_CCA] box_geq_value (t:timestamp[const]) (i:index) :
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

lemma [Privacy_CCA] box_unchanged :
  forall i,
  happens(MOP) => box(i)@pred(MOP) = box(i)@pred(MVP).
Proof.
  intro i Hap.
  case happens (MVC i) => H.
  +
  have ? := Trace.any_MOP MVP.
  have ? := Trace.MVC_MVP i.
  have -> : box(i)@pred MOP = box(i)@MVC i. {
    apply box_geq_value (pred MOP) i => //.
  }.
  have -> : box(i)@pred MVP = box(i)@MVC i. {
    apply box_geq_value (pred MVP) i; 1,2: constraints.
  }
  apply eq_refl.
  + rewrite 2!box_nan //.
    by have ? := Trace.happens_MVP.
Qed.

lemma [Privacy_CCA] box_val :
forall i,
happens(MVP,MVC(i)) =>
 (box(i)@ pred MVP =  box(i)@MVC(i)).
Proof.
intro *.
simpl.
  have Rw := box_geq_value (pred MVP) i.
  apply Rw. 
  - auto.
  - have ? // := Trace.MVC_MVP i. 
Qed.



(*******************************************************************************
## Lemmas to track values of mutable variables count
********************************************************************************)


lemma [Privacy_CCA] count_nan (t:timestamp[const]) (i:index):
(not (happens((MOC i)))) => happens(t) => (count(i)@t = zero).
Proof.
  intro Hap.
  induction t.
  intro *.
  have Hind := H (pred t).
  clear H.
  case t; intro Ht; try (
  rewrite /count;
  rewrite Ht in Hind;
  rewrite Ht in Hap0;
  by apply Hind).
  - by rewrite /count.
  - destruct Ht.
    rewrite Ceq in *.
    rewrite /count.  
    by apply Hind. 
  - destruct Ht.
    rewrite Ceq in *.
    case i = j; intro Case.
    * by rewrite Case in *. 
    * rewrite /count.
      rewrite if_false; auto.
Qed.

lemma [Privacy_CCA] count_lt_value (t:timestamp[const]) (i:index) :
  happens(t,MOC i) =>  t < MOC i  => count(i)@t = zero.
Proof.
  induction t.
  intro *.
  destruct H0 as [Hc Ht].
  case t; intro Hind => //;
  try (
    have Hp := H (pred(t));
    rewrite !impl_true in Hp => //
  ).
  destruct Hind as [i0 Ceq].
  rewrite Ceq.
  case i = i0 ; intro Heq.
  - by rewrite Ceq Heq in Clt.
  - rewrite /count.
    rewrite if_false => //. 
Qed.

lemma [Privacy_CCA] count_geq_value (t:timestamp[const]) (i:index) :
  happens(t) => MOC i <= t =>
  count(i)@ t = count(i)@MOC i.
Proof.
  induction t.
  intro *.
  case t = init => //.
  intro Heq.
  case t = MOC i. intro Meq. rewrite Meq. auto.
  intro Hmc.
  case t < MOC i; 1: constraints.
  intro Hleq.
  have Hp := H (pred t).
  rewrite !impl_true in Hp; 1,2,3: constraints.
  have -> : count(i)@t = count(i)@pred t. {
    case t; intro Ht //. 
    destruct Ht as [i0 Ceq].
    case i = i0; 1: auto.
    intro *.
    by rewrite if_false.
  }.
  apply Hp.
Qed.

lemma [Privacy_CCA] count_val :
forall i,
happens(MOP,MOC(i)) =>
 (count(i)@ pred MOP = count(i)@MOC(i)).
Proof.
intro *.
simpl.
  have Rw := count_geq_value (pred MOP) i.
  apply Rw. 
  - auto.
  - have ? // := Trace.any_MOP (MOC i). 
Qed.   



lemma [Privacy_CCA] exec_val (t:_): 
happens(t) => exec@t = true.
Proof.
induction t.
intro *.
case t;  try( intro Eq; rewrite /exec; by rewrite H).
* auto.
* intro Eq. destruct Eq. rewrite /exec. by rewrite H.
* intro Eq. destruct Eq. rewrite /exec. by rewrite H.
Qed.



(*******************************************************************************
## Lemmas to track values of mutable variables BB
********************************************************************************)


lemma [Privacy_CCA] bb_val (t:timestamp): 
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



lemma [Privacy_CCA] bb_val_mvp :
happens(MVP,BBS) => MVP < BBS => ((BB@BBS) = read (att (frame@MVP))).
Proof.
intro Hap Leq.

rewrite /BB /bb /input.
have -> : MVP = pred BBS. by apply Trace.rw_MVP_BBS. 
auto.
Qed.


lemma [Privacy_CCA] bb_aopening : 
happens(Aopening,BBS) => 
BB@pred Aopening = if happens(BBS) then (if (BBS < Aopening) then (BB@BBS) else witness) else witness. 
Proof.
intro Hap.
rewrite if_true. auto.
have H :  BBS < Aopening by apply Trace.BBS_Aopening.
rewrite if_true. auto.
by rewrite -bb_val.
Qed. 

lemma [Privacy_CCA] bb_bopening : 
happens(Bopening,BBS) => 
BB@pred Bopening = if happens(BBS) then (if (BBS < Bopening) then (BB@BBS) else witness) else witness. 
Proof.
intro Hap.
rewrite if_true. auto.
have H :  BBS < Bopening by apply Trace.BBS_Bopening.
rewrite if_true. auto.
by rewrite -bb_val.
Qed. 

end Macro.
