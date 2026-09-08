include Core.
include[admit] "indices.sp".
include[admit] "DHLib.sp".
include[admit] "model.sp".
include[admit] "utils.sp".

(**************************************)
(* Helping Lemmas on action orderings *)
(**************************************)

lemma firstIzero @system:S (tau:timestamp) : tau < Izero => tau = init.
Proof.
  smt.
Qed.

exact lemma [S/left] R_init (i:index) : (R i = init) = false.
Proof.
  auto.
Qed.
hint rewrite R_init.

exact lemma [S/left] I_init (i:index) : (I i = init) = false.
Proof.
  auto.
Qed.
hint rewrite I_init.

lemma contrapositive_orderR @system:S (i,j : index) :
  R i < R j => i ~< j.
Proof.
smt.
  (* intro I.  *)
  (* have T := ind_tricho i j.  *)
  (* case T. *)

  (* - auto. *)
  (* - auto. *)
  (* - have Neq := initR j _ => //. by apply (orderR j i _ Neq) in T. *)
Qed.


lemma R_bigger_one  @system:S (i : index) : happens(R i) => i = ind_one || ind_one ~< i.
Proof. 
smt.
(* have [C|C|C] := ind_tricho ind_one i => //. *)

(* intro Hap. *)
(* have Neg := initR i Hap. *)
(* have T := ind_order2 ind_one i ind_diff. *)
(* have [C2|C2|C2] := ind_tricho ind_zero i => //. *)
(* by have _ := ind_min i. *)
 Qed. 

lemma I_bigger_one  @system:S (i : index) : happens(I i) => i = ind_one || ind_one ~< i.
Proof.
smt.
(* have [C|C|C] := ind_tricho ind_one i => //. *)

(* intro Hap. *)
(* have Neg := initI i Hap. *)
(* have T := ind_order2 ind_one i ind_diff. *)
(* have [C2|C2|C2] := ind_tricho ind_zero i => //. *)
(* by have _ := ind_min i. *)
Qed. 

lemma next_orderR @system:S (i,j : index) :
  R i < R j =>  j <> ind_one.
Proof. 
smt.
(* intro Ord. *)
(* have Oij := contrapositive_orderR i j Ord. *)
(* intro Eq. *)
(* rewrite Eq in Oij. *)
(* have Noi := initR i _ => //. *)
(* have Noj := initR ind_one _ => //. *)

(* have T := ind_order3 i ind_one Noi Noj Oij. *)


(* by have _ := ind_min (ind_pred i). *)
 Qed. 

lemma contrapositive_orderI @system:S (i,j : index) :
  I i < I j => i ~< j.
Proof.
smt.
  (* intro I. *)
  (* have T := ind_tricho i j. *)
  (* case T. *)

  (* - auto. *)
  (* - auto. *)
  (* - have Neq := initI j. by apply (orderI j i _) in T. *)
Qed.



lemma next_orderI @system:S (i,j : index) :
  I i < I j =>  j <> ind_one.
Proof.
smt.
(* intro Ord. *)
(* have Oij := contrapositive_orderI i j Ord. *)
(* intro Eq. *)
(* rewrite Eq in Oij. *)
(* have Noi := initI i _ => //. *)
(* have Noj := initI ind_one _ => //. *)

(* have T := ind_order3 i ind_one Noi Noj Oij. *)


(* by have _ := ind_min (ind_pred i). *)
 Qed. 

lemma prevR_R_1 @system:S :
  happens (R ind_one) =>
  not (exists j, R j < R ind_one).
Proof.
smt.
  (* intro Hap [j H]. *)
  (* have NoZ := initR j _ => //. *)
  (* have T := ind_tricho j ind_zero. *)
  (* case T. *)
  (* - by apply ind_min j. *)
  (* - auto. *)
  (* - have _ := contrapositive_orderR j ind_one H. *)
  (*   search ind_pred _. *)
  (*  by  have _ := ind_order2 ind_one j ind_diff. *)
Qed.


lemma prevI_I_1 @system:S :
  happens (I ind_one) =>
  not (exists j, I j < I ind_one).
Proof.
smt.
  (* intro Hap [j H]. *)
  (* have T := ind_tricho j ind_zero. *)
  (* have NoZ := initI j _ => //. *)
  (* case T. *)
  (* - by apply ind_min j. *)
  (* - auto. *)
  (* - apply contrapositive_orderI in H. *)
  (*  by  have _ := ind_order2 ind_one j ind_diff. *)
Qed.

lemma is_exec  @system:S t:
    happens(t) => exec@t.
Proof.
  induction t.
  intro t IH Hap. 
  case t; smt. 
Qed.



(**************************************)
(********** getRi and getIi ***********)
(**************************************)

(* We define two function `getRi` and `getIi` such that
   `getRi tau = i` iff `i` is the index of the previous
   action `R` was the  before `tau`
   (`0` if there is no action `R` before), and resp. for `getIi`.
   These function are used to write our main property in `secret.sp`. *)

let rec getRi @system:S (t:timestamp) with
  | R i when happens(t) -> i 
  | I i when happens(t)  -> getRi (pred t)
  | Cor _ when happens(t)  -> getRi (pred t)
  | RO _ when happens(t)  -> getRi (pred t)
  | RO' _ when happens(t)  -> getRi (pred t)
  | Izero when happens(Izero) -> ind_zero
  | init -> ind_zero
  | _ when not(happens(t)) -> ind_zero.
Proof.
  repeat split; constraints.
Qed.

let rec getIi @system:S (t:timestamp) with
  | I i when happens(t) -> i
  | R i when happens(t)  -> getIi (pred t)
  | Cor _ when happens(t)  -> getIi (pred t)
  | RO _ when happens(t)  -> getIi (pred t)
  | RO' _ when happens(t)  -> getIi (pred t)
  | Izero when happens(Izero) -> ind_zero
  | init -> ind_zero
  | _ when not(happens(t)) -> ind_zero.
Proof.
  repeat split; constraints.
Qed.

lemma same_getRi @system:S (tau, tau' : timestamp) :
  tau < tau' =>
  (not (exists j, tau < R j && R j < tau')) =>
  getRi tau = getRi (pred tau').
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = pred tau' || tau < pred tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case (pred tau') ; 
    try (intro [i R]; by rewrite R /getRi).
  - auto.
  - smt. 
  - smt.
Qed.

lemma init_getRi @system:S :
  happens (R ind_one) =>
  getRi init = getRi(pred (R ind_one)). 
Proof.
  intro Hap.
  apply same_getRi init (R ind_one); 1: auto.
  smt.
Qed.

lemma getRi_pred @system:S (i : index) :
  happens (R i) =>
  getRi (pred (R i)) = (ind_pred i).
Proof.
  intro Hap.
  have C : i = ind_one || i <> ind_one; 1: auto.
  case C.
  - rewrite C in *.
    by rewrite -init_getRi.
  - rewrite -(same_getRi (R(ind_pred i))).
    + smt ~prover:CVC5 ~steps:100000.
    + smt ~prover:Z3.
    + smt ~prover:Z3.
Qed.

lemma same_getIi @system:S (tau, tau' : timestamp) :
  tau < tau' =>
  (not (exists j, tau < I j && I j < tau')) =>
  getIi tau = getIi (pred tau').
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = pred tau' || tau < pred tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case (pred tau') ; 
    try (intro [i R]; by rewrite R /getIi).
  - auto.
  - smt. 
  - smt.
Qed.

lemma init_getIi @system:S :
  happens (I ind_one) =>
  getIi init = getIi(pred (I ind_one)). 
Proof.
  intro Hap.
  apply same_getIi init (I ind_one); 1: auto.
  smt.
Qed.

lemma getIi_pred @system:S (i : index) :
  happens (I i) =>
  getIi (pred (I i)) = (ind_pred i).
Proof.
  intro Hap.
  have C : i = ind_one || i <> ind_one; 1: auto.
  case C.
  - rewrite C in *.
    by rewrite -init_getIi.
  - rewrite -(same_getIi (I(ind_pred i))).
    + smt ~prover:CVC5 ~steps:100000.
    + smt ~prover:Z3.
    + smt ~prover:Z3.
Qed.

lemma getRi_notR @system:S (tau : timestamp) :
  happens(tau) =>
  (forall i, tau <> R i) =>
  getRi tau = getRi (pred tau).
Proof.
  intro Hap.
  case (tau) ; 
    try (intro [i R]; by rewrite R /getRi).
  - smt. 
  - smt. 
  - smt.
Qed.

lemma getIi_notI @system:S (tau : timestamp) :
  happens(tau) =>
  (forall i, tau <> I i) =>
  getIi tau = getIi (pred tau).
Proof.
  intro Hap.
  case (tau) ; 
    try (intro [i R]; by rewrite R /getIi).
  - smt. 
  - smt. 
  - smt.
Qed.



(**************************************)
(******* RKRsend utility lemmas *******)
(**************************************)

lemma same_RKRsend @system:S (tau, tau' : timestamp) :
  tau < tau' =>
  (not (exists j, tau < R j && R j < tau')) =>
  RKRsend@tau = RKRsend@(pred tau').
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = pred tau' || tau < pred tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case (pred tau') ; 
    try (intro [i R]; by rewrite R /RKRsend).
  - auto.
  - auto.
  - intro [i F].
    have H0 : (false => RKRsend@(pred (pred tau')) = RKRsend@(pred tau')); 1: auto.
    apply H0.
    clear H0.
    apply H.
    by exists i.
Qed.



lemma init_RKRsend @system:S :
  happens (R ind_one) =>
  RKRsend@init = RKRsend@(pred (R ind_one)).
Proof.
  intro Hap.
  apply same_RKRsend init (R ind_one).
  + auto.
  + smt.
(*  intro [j H].
  apply prevR_R_1; 1: auto.
  by exists j. *)
Qed.


lemma RKRsend_pred @system:S (i : index) :
  happens (R i) =>
  RKRsend@(pred (R i)) = if i = ind_one then s_init else RKRsend@(R (ind_pred i)).
Proof.
  intro Hap.
  have C : i = ind_one || i <> ind_one; 1: auto.
  case C.
  - rewrite if_true; 1: auto.
    rewrite C in *.
    by rewrite -init_RKRsend.
  - rewrite if_false; 1: auto.
    rewrite -(same_RKRsend (R(ind_pred i))).
    + smt.
    + smt.
    + auto.
    (*have NoZ := initR i _ => //. 
      intro [j [H1 H2]].
      apply contrapositive_orderR in H1.
      apply contrapositive_orderR in H2.
      apply (ind_order2 i j NoZ).
      auto. *)
    (* apply orderR; 1: auto. *)
    (*   intro Eq. rewrite /ind_zero in Eq. apply ind_inj in Eq => //. apply ind_diff. *)

    (*   apply ind_order1; 1: auto. *)
Qed.


(**************************************)
(******* RKIsend utility lemmas *******)
(**************************************)

lemma same_RKIsend @system:S (tau, tau' : timestamp) :
  tau < tau' =>
  (not (exists j, tau < I j && I j < tau')) =>
  RKIsend@tau = RKIsend@(pred tau').
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = pred tau' || tau < pred tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case (pred tau') ; 
    try (intro [i R]; by rewrite R /RKIsend).
  - auto.
  - auto.
  - smt.
(* intro [i F].
    have H0 : (false => RKIsend@(pred (pred tau')) = RKIsend@(pred tau')); 1: auto.
    apply H0.
    clear H0.
    apply H.
    by exists i.*)
Qed.



lemma init_RKIsend @system:S :
  happens (I ind_one) =>
  RKIsend@init = RKIsend@(pred (I ind_one)).
Proof.
  intro Hap.
  apply same_RKIsend init (I ind_one); 1: auto.
  smt.
(*  intro [j H].
  apply prevI_I_1; 1: auto.
  by exists j. *)
Qed.


lemma RKIsend_pred @system:S (i : index) :
  happens (I i) =>
  RKIsend@(pred (I i)) = 
   if i = ind_one then 
        h(<s_init, ofG((g^(skR ind_zero))^(skI ind_zero))>,k)
   else RKIsend@(I (ind_pred i)).
Proof.
  intro Hap.
  have C : i = ind_one || i <> ind_one; 1: auto.
  case C.
  - rewrite if_true; 1: auto.
    rewrite C in *.
    by rewrite -init_RKIsend.
  - rewrite if_false; 1: auto.
    rewrite -(same_RKIsend (I(ind_pred i))).
    + smt.
    + smt.
    + auto.
    (*+ intro [j [H1 H2]].
      apply contrapositive_orderI in H1.
      apply contrapositive_orderI in H2.
      apply (ind_order2 i j NoZ).
      auto.
    + smt. (* apply orderI; 1: auto. *)
      (* intro Eq. rewrite /ind_zero in Eq. apply ind_inj in Eq => //. apply ind_diff. *)

      (* apply ind_order1; 1: auto. *)*)
Qed.



(*****************************************)
(******* RKIreceive utility lemmas *******)
(*****************************************)


lemma same_RKIreceive @system:S (tau, tau' : timestamp) :
  tau < tau' =>
  (not (exists j, tau < I j && I j < tau')) =>
  RKIreceive@tau = RKIreceive@(pred tau').
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = pred tau' || tau < pred tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case (pred tau');
    3,5,6,7: intro [i R];
    by rewrite R /RKIreceive.
  - auto.
  - auto.
  - smt. 
(*intro [i F].
    have H0 : (false => RKIreceive@(pred (pred tau')) = RKIreceive@(pred tau')); 1: auto.
    apply H0.
    clear H0.
    apply H.
    by exists i.*)
Qed.

lemma init_RKIreceive @system:S :
  happens (I ind_one) =>
  RKIreceive@init = RKIreceive@(pred (I ind_one)).
Proof.
  intro Hap.
  apply same_RKIreceive init (I ind_one); 1: auto.
  smt.
(*  intro [j H].
  apply prevI_I_1; 1: auto.
  by exists j. *)
Qed.

lemma RKIreceive_pred @system:S (i : index) :
  happens (I i) =>
  RKIreceive@(pred (I i)) = if i = ind_one then s_init  else RKIreceive@(I (ind_pred i)).
Proof.
  intro Hap.
  have C : i = ind_one || i <> ind_one; 1: auto.
  case C.
  - rewrite if_true; 1: auto.
    rewrite C in *.
   by  rewrite -init_RKIreceive.  
  - rewrite if_false; 1: auto.
    rewrite -(same_RKIreceive (I(ind_pred i))).
    + smt.
    + smt. 
    + auto.
(* intro [j [H1 H2]]. *)
      (* apply contrapositive_orderI in H1. *)
      (* apply contrapositive_orderI in H2. smt. *)
(*      apply (ind_order2 i j NoZ).
      auto. *) (* apply orderI; 1: auto. smt. smt. *)
(*      intro Eq. rewrite /ind_zero in Eq.  apply ind_inj in Eq => //. apply ind_diff.
      apply ind_order1; 1: auto. *)
Qed.



(*****************************************)
(******* RKRreceive utility lemmas *******)
(*****************************************)


lemma same_RKRreceive @system:S (tau, tau' : timestamp) :
  tau < tau' =>
  (not (exists j, tau < R j && R j < tau')) =>
  RKRreceive@tau = RKRreceive@(pred tau').
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = pred tau' || tau < pred tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case (pred tau');
    4,5,6,7: intro [i R];
    by rewrite R /RKRreceive.
  - auto.
  - auto.
  - smt.
    (*intro [i F].
    have H0 : (false => RKRreceive@(pred (pred tau')) = RKRreceive@(pred tau')); 1: auto.
    apply H0.
    clear H0.
    apply H.
    by exists i. *)
Qed.

lemma init_RKRreceive @system:S :
  happens (R ind_one) =>
  RKRreceive@init = RKRreceive@(pred (R ind_one)).
Proof.
  intro Hap.
  apply same_RKRreceive init (R ind_one); 1: auto.
  smt.
(*  intro [j H].
  apply prevR_R_1; 1: auto.
  by exists j. *)
Qed.

lemma RKRreceive_pred @system:S (i : index) :
  happens (R i) =>
  RKRreceive@(pred (R i)) = if i = ind_one then s_dum  else RKRreceive@(R (ind_pred i)).
Proof.
  intro Hap.
  have C : i = ind_one || i <> ind_one; 1: auto.
  case C.
  - rewrite if_true; 1: auto.
    rewrite C in *.
   by  rewrite -init_RKRreceive.  
  - rewrite if_false; 1: auto.
    rewrite -(same_RKRreceive (R(ind_pred i))).
    + smt.
    + smt.
    + auto.
    (*have NoZ := initR i _ => //.
    intro [j [H1 H2]]. *)
      (* apply contrapositive_orderR in H1. *)
      (* apply contrapositive_orderR in H2. smt. *)
(*      apply (ind_order2 i j NoZ).
      auto. *)
    (* apply orderR; 1: auto. smt. smt. *)
(*      intro Eq. rewrite /ind_zero in Eq.  apply ind_inj in Eq => //. apply ind_diff.
      apply ind_order1; 1: auto. *)
Qed.

(*********************************)
(* HealthyR and HealthyI utilities  *)
(*********************************)

lemma healthyR_zero @system:S :
  healthyR (ind_zero)  = true.
Proof.
 by rewrite /healthyR or_true_left. 
Qed.

lemma healthyI_zero @system:S (i:index):
  i=ind_zero =>  healthyI (i)  = true.
Proof.
  intro ->.
  rewrite /healthyI safeI_zero /=  or_true_left. 
  rewrite /syncRI /=.
  apply healthyR_zero.
  auto.
Qed.


(*********************************)
(* SyncRI and SyncIR are correct *)
(*********************************)


lemma syncIRone @set:S :  syncIR (ind_zero) = (gI@R(ind_one) = g ^ skI ind_zero) .
Proof.
smt.
(* rewrite /syncIR or_false_right. *)

(* + intro [Ord C]. *)
(* have Not := initI ind_zero _. auto.  *)
(* auto. *)

(* + auto. *)
Qed.

lemma SyncIoth @set:S tau :
forall i:index,
(tau=I i => happens(I i) => syncRI (i) => RKIreceive@I i = RKRsend@R i)
 (*  RKIsend@I i -1 = RKRreceive@R i => RKIreceive@I i = RKRsend@R i *)

&&
(tau = (R (ind_succ i)) =>  happens(R i) => syncIR (i) => RKRreceive@R (ind_succ i) = RKIsend@I (i))
 (*   RKRreceive@R i = RKIreceive@I i = =>  RKRreceive@R (ind_suc i) = RKIsend@I (i)*)
. 
Proof.
induction tau.
intro tau IH i.

split. 
 + intro Ht Hap S.

  have Not : (i <> ind_zero) by smt.

  rewrite /syncRI or_false_left // in S.
  destruct S as [S2 [S1 S3]].
  rewrite /RKIreceive /RKRsend S3.

  rewrite RKIsend_pred => //.

  case i=ind_one.
   ++ rewrite /RKRreceive. 
      rewrite RKRsend_pred => //. simpl. 
       intro Eq. rewrite Eq in *. rewrite if_true //. 
       rewrite /= syncIRone in S1.
       by rewrite /gRecR S1 exp_mult E_com.

   ++ intro Neg.
      rewrite !if_false //.
      smt.
       (* have Leq := ind_order1 i Not. *)
       (* have T := orderI (ind_pred i) i Hap _ Leq. *)
       (*  intro Eq.   rewrite /ind_zero in Eq. apply ind_inj in Eq => //. apply ind_diff. *)
       (*  have H := orderR (ind_pred i) i _ _ _ => //. *)
       (*  intro U. rewrite /ind_zero in U.         *)
       (*   have V := ind_inj i ind_one _ _ _ => //. *)
       (*   by apply ind_diff. *)

       (*  have [_ I] := IH (R (i)) (ind_pred i) _ => //.  *)
        
       (*  rewrite ind_succ_pred_eq in I => //. *)
       (*  by rewrite I => //.       *)


 + intro Ht Hap S.

  have Not : (i <> ind_zero) by smt.

  rewrite /syncIR or_false_left // in S.
  destruct S as [S2 [S1 S3]].
  rewrite /RKRreceive /RKIsend S3.

  rewrite RKRsend_pred => //.
  smt.
(*  rewrite if_false.
   { smt. }
(*   { intro Neq.
    by rewrite /ind_zero -Neq ind_pred_succ_eq in Not.        
   } *)
   smt.
(*    rewrite ind_pred_succ.

    have [I _] := IH (I ( i)) ( i) _   => //. 
    by rewrite I. *) *)
Qed.


lemma SyncRI @set:S i:
happens(I i) => syncRI (i) => RKIreceive@I i = RKRsend@R i.
Proof.
have [L _] := SyncIoth (I i) i.  
by apply L.
Qed.


lemma SyncIR @set:S i:
 happens(R i) => syncIR (i) => RKRreceive@R (ind_succ i) = RKIsend@I (i).
Proof.
have [_ R] := SyncIoth (R (ind_succ i)) i.  
by apply R.
Qed.


(*******************************************)
(* SyncRI and SyncIR implies that the      *)
(* attacker does not tamper DH public keys *)
(*******************************************)

lemma Sync_DHpub @set:S i:
  i <> ind_zero =>
  (syncIR (ind_pred i) => gI@R i = g ^ (skI (ind_pred i))) &&
  (syncRI i => gR@I i = g ^ (skR i)).
Proof.
  induction i.
  intro i IH I1.

  have H : (syncIR (ind_pred i) => gI@R(i) = g ^ skI (ind_pred i)). {
    intro S.
    case i = ind_one; intro I2.
    - rewrite I2 in *.
      clear I1 I2 IH.
      rewrite /syncIR -ind_o or_false_right in S; smt.
    - have [IH1 IH0] := IH (ind_pred i) _ _ ; 1: smt. {
        apply ind_to_leq.
        smt.
      }
      clear IH IH1.
      rewrite /syncIR or_false_left in S; 1: smt.
      destruct S as [S1 [S2 S3]].
      have R : ind_succ (ind_pred i) = i; 1: smt.
      apply IH0 in S2.
      rewrite /gSendI /gRecR S2 exp_mult E_com -exp_mult R in S3.
      by apply inv_exp in S3.
  }
  split; 1: auto.
  intro S.
  rewrite /syncRI or_false_left in S; 1: smt.
  destruct S as [S1 [S2 S3]].
  rewrite /gSendR /gRecI H in S3; 1: auto.
  rewrite exp_mult E_com -exp_mult in S3.
  by apply inv_exp in S3.
Qed.


global lemma Heal_DHpubR @set:S/left (i:index [const]) : 
  [happens(R i)] -> 
  [HealthyR i] ->
  [not(HealthyR (ind_pred i)) || SyncIR (ind_pred i)] ->
  [(not (HealthyI (ind_pred i)) || not(SyncIR(ind_pred i)))] -> 
      [safeR i && safeI (ind_pred i) &&  
       gI@R(i) = g ^ skI (ind_pred i) && 
       gSendR@R i = g^(skI (ind_pred i) ** skR i) &&
       i <> ind_zero &&
       (I (ind_pred i ) <  R i || (ind_pred i=ind_zero && Izero < R i))
].
Proof.
  intro Hap H2 H1 H.

  have [_ _ gI _] : safeR i && safeI (ind_pred i) && 
       gI@R(i) = g ^ skI (ind_pred i) && 
       gSendR@R i = g^(skI (ind_pred i) ** skR i).
  {
  case SyncIR (ind_pred i).
  ++ intro S.
      localize H as H' => {H}.  
      localize H1 as H1' => {H1}.  
      localize H2 as H2' => {H2}.  
     rewrite S /= in H'.       
     rewrite -healthyI_to_HealthyI in H'.
      
     rewrite -healthyR_to_HealthyR /healthyR or_false_left in H2'; 1: smt ~no_macros.
     rewrite syncIR_to_SyncIR if_true // in H2'. 
     destruct H2' as [_ H3].
     rewrite or_false_left in H3; 1: smt ~no_macros.
     destruct H3 as [_ H3].
     rewrite /gSendR H3. by simpl.
      ++ intro S.   clear H.
      localize H2 as H2' => {H2}.  
     rewrite -healthyR_to_HealthyR /healthyR or_false_left in H2'; 1: smt ~no_macros.

     rewrite syncIR_to_SyncIR S /= in H2'.       
        
     rewrite healthyR_to_HealthyR or_false_left in H2'; 1: smt ~no_macros.
     destruct H2' as [_ [_ H3]].
     rewrite /gSendR H3. by simpl. 
  }

   have _ : i <> ind_zero.
     {
     intro Eq.
     localize H as H'. 
     localize H1 as H1'.
     rewrite Eq in *.
     rewrite -healthyR_to_HealthyR -syncIR_to_SyncIR in H1'.
     rewrite -healthyI_to_HealthyI -syncIR_to_SyncIR in H'.
     smt.
     }

     have _ : I (ind_pred i ) <  R i || (ind_pred i=ind_zero && Izero < R i). (* otherwise freshness de b (ind_pred i) *) 
       {         
         apply f_apply dlog in gI. simpl.
         rewrite eq_sym in gI.
         fresh gI => //; smt ~no_macros.
       }
     auto.
Qed.


global lemma Heal_DHpubI @set:S/left (i:index[const]) : 
  [happens(I i)] -> 
  [HealthyI i] ->
  [not(HealthyI (ind_pred i)) || SyncRI (i)] ->
  [not (HealthyR (i)) || not(SyncRI i)] -> 
      [safeR i && safeI i &&  
       gR@I(i) = g ^ skR i && 
       gSendI@I i = g^( skR i ** skI i) && 
       i <> ind_zero &&
       R i < I i
].
Proof.
  intro Hap H2 H1 H.

  have [_ _ gR _] : 
       safeR i && safeI i &&  
       gR@I(i) = g ^ skR i && 
       gSendI@I i = g^( skR i ** skI i).
  {
  case SyncRI i.
  ++ intro S.  
      localize H as H' => {H}.  
      localize H1 as H1' => {H1}.  
      localize H2 as H2' => {H2}.  
     rewrite S /= in H'.       
     rewrite -healthyR_to_HealthyR in H'.
      
     rewrite -healthyI_to_HealthyI /healthyI in H2'. 
     rewrite syncRI_to_SyncRI if_true // in H2'.

     destruct H2' as [_ H3].
     rewrite or_false_left in H3; 1: smt ~no_macros.
     destruct H3 as [_ H3].
     rewrite /gSendI H3. by simpl.
      ++ intro S.   clear H.
      localize H2 as H2' => {H2}.  
      rewrite -healthyI_to_HealthyI /healthyI in H2'. 
      localize H1 as H1' => {H1}.  
      rewrite S /= in H1'.        
     rewrite syncRI_to_SyncRI S /= in H2'.       
        
     rewrite healthyI_to_HealthyI or_false_left in H2'; 1: smt ~no_macros.
     destruct H2' as [_ [_ H3]].
     rewrite /gSendI H3. by simpl. 
   }

  have _ : i <> ind_zero.
     {
     intro Eq.
     localize H as H'. 
     localize H1 as H1'.
     rewrite Eq in *.
     rewrite -healthyR_to_HealthyR -syncRI_to_SyncRI in H'.
     rewrite -healthyI_to_HealthyI -syncRI_to_SyncRI in H1'.
     smt.
     }

     have _ : R i < I i. (* otherwise freshness de b (ind_pred i) *) 
       {         
         apply f_apply dlog in gR. simpl.
         rewrite eq_sym in gR.
         fresh gR => //; smt ~no_macros.
       }
 auto.
Qed.


lemma healthy_from_safe @system:S (p:index*bool):
  (forall j, (j ~< (p#1) || j=p#1) => safeI j && safeR j)
  =>  (not(p#2) => HealthyR (p#1))
    &&  (p#2 => HealthyI (p#1)).
Proof.

induction p.
intro p IH.

intro Safe.

case (p#2).
  + simpl. 
    intro P2.

    rewrite -healthyI_to_HealthyI /healthyI.

    split.
    ++ by have S := Safe (p#1).

    ++ left.  
       case syncRI (p#1).
       +++ intro S.
           have [IH0 _] :=  IH (p#1,false) _ _. 
           by simpl. 
           rewrite pair_order. by right.

           simpl.  
           by rewrite healthyR_to_HealthyR.
       +++ intro S.
           simpl.
           have [_ IH0] :=  IH (ind_pred (p#1),true) _ _. 
           intro j Ord. have _ := Safe j _. simpl.  smt.
           by simpl. 
           rewrite pair_order. left. smt.
           by rewrite healthyI_to_HealthyI.           
  + simpl.
    intro NP2. 

    rewrite -healthyR_to_HealthyR /healthyR.

    case p#1 = ind_zero. by auto.

    intro nZ /=. 
    split.
    ++ by have S := Safe (p#1).

    ++ left.  
       case syncIR (ind_pred (p#1)).
       +++ intro S.
           have [IH0 _] :=  IH (ind_pred (p#1),true) _ _. 
           intro j Ord. have _ := Safe j _. simpl.  smt.
           by simpl. 
           rewrite pair_order. left. smt. 

           simpl.  
           by rewrite healthyI_to_HealthyI.
       +++ intro S.
           simpl.
           have [_ IH0] :=  IH (ind_pred (p#1),false) _ _. 
           intro j Ord. have _ := Safe j _. simpl.  smt.
           by simpl. 
           rewrite pair_order. left. smt.
           by rewrite healthyR_to_HealthyR.           
Qed.
