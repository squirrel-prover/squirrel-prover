include Core.
include NonDeduction.

include[admit] "indices.sp". 
include[admit] "DHLib.sp".
include[admit] "model.sp".
include[admit] "utils.sp".
include[admit] "trace.sp".
include[admit] "oracles.sp".
include[admit] "simulation.sp".
include[admit] "non_collision.sp".
include[admit] "secrecy_p1.sp".


(*******************************************)
(* Case 2: ORKRsend ORKIreceive is maximum *)
(*******************************************)	

(* Simplification : The trace alternate R and I and maximal tau is R
               Rlice                     Iob
 -----------------------------------------------------------
                r1*          c1* <--h'-- r1?*
                |                        |
                |h                       |h
                V                        V
                r2?* --h'--> c2*         r2*
                |                        |   tau1l < tau2l
............... |h ......                |h  taur  < tau2l
                V        .               V
                r3*       .  c3* <--h'-- r3?*
                |          .             |
                |h          ............ |h ...............
                V                        V
                r4! --h'--> c4           r4
 *)
(* We will have to eliminate the extra hash h produced by ORKRsend or
   ORKIreceive on the left hand side.  Depending on whether tau0 is R
   i, I i, or something else, either a h(RKRsend), h'(RKIsend), or
   nothing, is added on the left hand side.  The difficult cases are
   the first two: we will have to eliminate the extra h' hash produced
   by OCKRsend or OCKIsend. *)

global lemma Secret_case2 @set:S/left (tau0:timestamp[const]):
  [init < tau0]
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur < tau0 || (taur = tau0 && t < 3)] ->
      (Secret_prop t (pred tau0) (pred tau0) tau0 (pred tau0) taur))
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur < tau0 || (taur = tau0 && t < 3)] ->
      (Secret_prop t (pred tau0) tau0 tau0 (pred tau0) taur)).
Proof.
  intro HI HP taur side Htaur.
  rewrite /Secret_prop /Secret_target /=.
  intro Hhap n n2 Heal.

  ghave [[i Htau] | [i Htau] | Zt] :
      (Exists (i:index [const]), [tau0=R i]) 
   \/ (Exists (i:index [const]), [tau0=I i]) 
   \/ (Forall (i:index [const]), [tau0<>R i && tau0<>I i ]).
   
   * (* proving the disjunction *)
     case tau0; try (   (intro [j R] + intro j); right; right; intro j'; constraints ).  
     intro [i R]. left. by exists i.
     intro [i I]. right. left. by exists i.


   (**********************************)
   (* Case 2.1: tau0=R i is maximum *)
   (**********************************)

     (* Here, we have to scale ORKRsend one step back. *)
     (* If HealthyR i, this is trival, since nothing is added at tau2l. *)
     (* Otherwise, the attacker gets an extra RKRsend from ORKRsend when not(HealthyR i) 

        We do the following case disjunction,
        where we use prf to get rid of the hash,
        either because some inputs of the hash are secret,
        or because we get a fresh hash for which we can already test equlity.


        syncIR i-1   HealthyR i-1  HealthyI i-1
          x            true           x        -> RKRreceive@R i is secret, by induction. 
         true          false         true    -> RKRreceive@R i = RKIsend@I i-1 secret by induction


         false         false           x            -> RKRreceive@R i is public from ORKRreceive, call prf ~equality
         true          false         false    -> RKRreceive@R i = RKIsend@I i-1 public, call prf equality




      *)
      
   * (* first, we isolate the value added to ORKRsend, the rest does not change. *)
     rewrite Htau /Oracles.
     deduce with (ORKRsend_split i); [1: constraints].  
     rewrite stable_ORKIsend; [1: constraints].


     (* Depending on HealthyR i, either RKRsend@R i or nothing is added *)
     ghave [H|H] : [ not(HealthyR i) || (HealthyR i)]; 1: rewrite -impl_charac; intro _; assumption.  

     (* Case not HealthyR i:
        this is the case where we must remove an RKRsend *)
     ** rewrite H /RKRsend /=. 
        rewrite /gSendR  => //.
        
        (* just as in case 1, we unroll a little before applying prf *)
        rewrite expand_rhs; [1:constraints]. 
        rewrite expand_ORKRreceive. 

        rewrite /Opublic.

 
        (* depending on whether SyncIR (i - 1) and HealthyI (i - 1) hold, the reason
           why prf can be applied changes -- see comment at the beginning of case 2. *)
        ghave [H2|H3] :
          [ ( (HealthyR  (ind_pred i) && not (SyncIR (ind_pred i)) )  || (SyncIR (ind_pred i) && HealthyI (ind_pred i)))
          || not  ( (HealthyR  (ind_pred i) && not (SyncIR (ind_pred i)) ) || (SyncIR (ind_pred i) && HealthyI (ind_pred i)))]; 1: rewrite or_comm -impl_charac; intro _; assumption.
        

         (* case RKIsend@ I (i-1) is secret *)
         *** prf ~left ~under_hash 17.
           + { (* first subgoal: phi_prf *)
               repeat split.
               ++ have Neq := NoColRKRsendRKRreceive (pred (R i)) (R i) _; [1:constraints]. 
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro i0 _ _.
                  have Neq := NoColRKRsendRKRreceive (pred (R i0)) (R i) _; [1:constraints].
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq in Neq; by simpl.
               ++ have Neq := PIR_R (ind_pred i, true). 
                  rewrite /getR /pair_init /stR /getR /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)
               ++ intro j _ _.
                  have Neq := NoColRKRsendRKRreceive (pred (R j)) (R i) _; [1:constraints].  
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j _ _ Eq.  
                  localize Htaur as C.
                  case C.
                   +++ have Neq := NoColRKRreceive i j _ _; [1,2: constraints]. 
                       apply (f_apply fst) in Eq; simpl; rewrite Eq /RKRreceive neq_irrefl in Neq. assumption.
                   +++ smt ~no_macros.
               ++ intro j _ _ _ Eq.
                  have U : RKRsend@R i = RKIreceive@I j.
                  by rewrite /RKRsend /RKIreceive Eq /=.
                  by have _ := NoColIThenR i j _; [1:constraints].
               ++ intro j _ _ _ Eq. 
                  have U : RKRreceive@R i = RKIreceive@I j. 
	          apply (f_apply fst) in Eq. rewrite /= in Eq.
                  by rewrite /RKIreceive Eq /=.
                  by have S := NoColRKRreceiveRKIreceive (R i) (I j) _; [1:constraints].
               ++ have Neq := PIR_R (ind_pred i, true).
                  rewrite /getR /pair_init /stR /getR /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)
               ++ intro j _ _ _ _ Eq. 
                  have Neq := NoColRKRsendRKRreceive (pred (R j)) (R i) _; [1:constraints].
                  apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j _ _ _ _ T Eq. 
                  have Neq := NoColIThenR i j _; [1:constraints].
                  have U : RKRsend@R i = RKIreceive@I j. 
                  by rewrite /RKRsend /RKIreceive Eq /=.
                  by rewrite U /= neq_irrefl in Neq. 
               ++ intro j I.
                  have I0 : RO j < R i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); 
                     try constraints.
                   }
                  intro Ded.      
                  apply (f_apply snd) in Ded. simpl.
                  rewrite /gI in Ded.
                  apply (f_apply toG) in Ded. simpl.
                  apply (f_apply dlog) in Ded. simpl.
                  rewrite E_com  in Ded.
                  apply mult_inv_l in Ded.
                  clear  Heal I H2 H.
                  fresh Ded.
                  +++ smt ~no_macros.
                  +++ auto.   
                  +++ smt ~no_macros.   
                  +++ smt ~no_macros. 
                  +++ smt ~no_macros. 
               ++ intro j I. (* RKRreceive <> RKRsend *)
                  have I0 : R j < R i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                   clear I.
                   have Neq := NoColRKRsendRKRreceive (pred (R j)) (R i) _; [1:constraints].
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption. 
               ++ intro j I. (* RKRreceive <> RKRreceive *)
                  have I0 : R j < R i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                   clear I.
                    have Neq := NoColRKRreceive i j _ _; [1,2:constraints].
                    intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j I. (* I j < R i and gI^a i = gRecI@I j is impossible,
                                fresh a i *)
                  have I0 : I j < R i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                     constraints.
                   }
                  intro Ded.      
                  apply (f_apply snd) in Ded; simpl.
                  rewrite /gI in Ded.                  
                  apply (f_apply dlog) in Ded; simpl.
                  rewrite E_com  in Ded.
                  apply mult_inv_l in Ded.
                  clear H H2 Heal I. (* speeds up smt *)
                  fresh Ded; clear Ded.
                  +++ smt ~prover:CVC5 ~no_macros.
                  +++ auto.
                  +++ intro [_ [[_ | _] _]]. smt ~prover:CVC5 ~no_macros. smt ~prover:CVC5 ~no_macros.
                  +++ intro [_ [[_ | _] _]]. smt ~prover:CVC5 ~no_macros. smt ~prover:CVC5 ~no_macros.
                  +++ smt ~prover:CVC5 ~no_macros.

               ++ have U := PIR_R (ind_pred i, true) _ _. 
                  by rewrite /pair_init.
                  rewrite /getR /=. smt ~no_macros. 
                  intro R I. clear R H H2.
                  apply (f_apply fst) in I. simpl.      
                  rewrite /stR /getR /= in U.
                  smt ~no_macros. (* i <> ind_zero *)

               ++ intro i0 I. (* RKRreceive <> RKIreceive *)
                  have I0 : I i0 < R i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                  clear I.
                  have S := NoColRKRreceiveRKIreceive (R i) (I i0) _. constraints.
                  intro T.  apply (f_apply fst) in T.  simpl. rewrite T neq_irrefl in S. assumption.
             }



           + (* second prf subgoal: the hashed message cannot be deduced *)
             case H2.
            
             ++ (* HealthyR i-1 so we have secrecy of RKRreceive@R i *)

                rewrite -expand_ORKRreceive.


               (* HP says: oracles@pred t0, pred t0, t0 *> secret@init *)
                have ZIH := (HP (R i) 2 _). simpl;right; rewrite Htau eq_refl_e; assumption.
              
                rewrite /Secret_prop /Secret_target /Oracles /Opublic in ZIH.
                have DedNIH := ZIH _ n n2 _; [1,2: by simpl]; clear ZIH.

                rewrite Htau /= in DedNIH.
                apply (ded_right fst). simpl.
                by apply DedNIH.



              ++ (* *)
             destruct H2 as [H2 H3].
             (* eliminate the case where i = 1 *)
             ghave HZ : ([i = ind_one || ind_one ~< i]); [1:smt ~no_macros].
             destruct HZ as [HZ | HZ].
             +++ (* case i = ind_one *)
                rewrite  HZ /= in *; clear HZ i.
                have HS := syncIRone.  simpl.
                rewrite syncIR_to_SyncIR H2 /= in HS.
                have RRR : RKRreceive@(R ind_one) = RKIsend@init.
                 { rewrite /RKRreceive /RKIsend /gRecR HS RKRsend_pred /=; [1:constraints].
                   by rewrite E_com. }
                rewrite RRR; clear RRR.

                (* we show that RKIsend is secret *)
                apply (ded_right fst).
                simpl.

               (* HP says: oracles@pred t0, pred t0, t0 *> secret@init *)
                have ZIH := (HP init 3 _) ; [1:auto].
              
                rewrite /Secret_prop /Secret_target /Oracles /Opublic in ZIH.
                have DedNIH := ZIH _ n n2 _; [1,2: by simpl]; clear ZIH.

                rewrite Htau /= in DedNIH.
                rewrite -expand_ORKRreceive.                
                by apply DedNIH.

             +++ (* case i > ind_one *)
                have HS := SyncIR (ind_pred i) _ . smt ~no_macros.
                have XX : ind_succ (ind_pred i) = i. apply ind_succ_pred.
                  
                  have O1 := ind_zero_one. 
                  by apply (ind_trans _ ind_one _).
                  
                rewrite syncIR_to_SyncIR H2 XX /= in HS.
                rewrite HS /=.
                rewrite -syncIR_to_SyncIR /syncIR /= in H2.
                have _ : (ind_pred i = ind_zero) = false.  smt ~no_macros.

                have ZIH := (HP (I (ind_pred i))) 3 _ ; [1:by simpl].
                rewrite /Secret_prop /Secret_target in ZIH.
                have DedNIH := ZIH _ n n2 _; [1,2:by simpl]; clear ZIH.

                clear H H2 H3 HS HZ Heal XX.
                apply (ded_right fst).
                simpl.
                rewrite /= Htau /Oracles /Opublic /ORKRreceive /RKRreceive in DedNIH.
                by apply DedNIH.
 
           + have ZIH := HP taur side _; [1:auto].
             rewrite /Secret_prop /Secret_target in ZIH.
             have DedNIH := ZIH _ n n2 _; [1,2:by simpl].
             rewrite -expand_rhs; [1:constraints]. 
             rewrite -expand_ORKRreceive.
             rewrite /Oracles /Opublic Htau in DedNIH.
             by apply DedNIH.


         *** rewrite not_or not_and in H3.             
             destruct H3 as [H1 H2].

         (*
             The equality test is deducible, since
             - If not(HealthyiR) && not(SyncIR), the OstRRecieve leaks the target
             - If syncIR && not(HealtyI i-1), then and then RKRreceive = RKIsend which is leaked
                                                         by OStISend. *)


             prf ~left ~equality 17.
             + { (* first subgoal: phi_prf *)
                 repeat split.
               ++ intro i0 _ _.
                  have Neq := NoColRKRsendRKRreceive (pred (R i0)) (R i) _; [1:constraints]. 
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ have Neq := PIR_R (ind_pred i, true). 
                  rewrite /getR /pair_init /stR /getR /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)
               ++ intro j _ _.
                  have Neq := NoColRKRsendRKRreceive (pred (R j)) (R i) _; [1:constraints].  
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j _ _ Eq.  
                  localize Htaur as C.
                  case C.
                   +++ have Neq := NoColRKRreceive i j _ _; [1,2: constraints]. 
                       apply (f_apply fst) in Eq; simpl; rewrite Eq /RKRreceive neq_irrefl in Neq. assumption.
                   +++ smt ~no_macros.
               ++ intro j _ _ _ Eq. 
                  have U : RKRsend@R i = RKIreceive@I j.
                  by rewrite /RKRsend /RKIreceive Eq /=.
                  by have _ := NoColIThenR i j _; [1:constraints].
               ++ intro j _ _ _ Eq. 
                  have U : RKRreceive@R i = RKIreceive@I j. 
	          apply (f_apply fst) in Eq. rewrite /= in Eq.
                  by rewrite /RKIreceive Eq /=.
                  by have S := NoColRKRreceiveRKIreceive (R i) (I j) _; [1:constraints].
               ++ have Neq := PIR_R (ind_pred i, true).
                  rewrite /getR /pair_init /stR /getR /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)
               ++ intro j _ _ _ _ Eq. 
                  have Neq := NoColRKRsendRKRreceive (pred (R j)) (R i) _; [1:constraints].
                  apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j _ _ _ _ T Eq. 
                  have Neq := NoColIThenR i j _; [1:constraints].
                  have U : RKRsend@R i = RKIreceive@I j. 
                  by rewrite /RKRsend /RKIreceive Eq /=.
                  by rewrite U /= neq_irrefl in Neq. 
               ++ intro j I.
                  have I0 : RO j < R i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); 
                     try constraints.
                   }
                  intro Ded.      
                  apply (f_apply snd) in Ded. simpl.
                  rewrite /gI in Ded.
                  apply (f_apply toG) in Ded. simpl.
                  apply (f_apply dlog) in Ded. simpl.
                  rewrite E_com  in Ded.
                  apply mult_inv_l in Ded.
                  clear  Heal I H2 H.
                  fresh Ded.
                  +++ smt ~no_macros.
                  +++ auto.   
                  +++ smt ~no_macros.   
                  +++ smt ~no_macros. 
                  +++ smt ~no_macros. 
               ++ intro j I. (* RKRreceive <> RKRsend *)
                  have I0 : R j < R i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                   clear I.
                   have Neq := NoColRKRsendRKRreceive (pred (R j)) (R i) _; [1:constraints].
                   intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption. 
               ++ intro j I. (* RKRreceive <> RKRreceive *)
                  have I0 : R j < R i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                   clear I.
                    have Neq := NoColRKRreceive i j _ _; [1,2:constraints].
                    intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j I. (* I j < R i and gI^a i = gRecI@I j is impossible,
                                fresh a i *)
                  have I0 : I j < R i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                     constraints.
                   }
                  intro Ded.      
                  apply (f_apply snd) in Ded; simpl.
                  rewrite /gI in Ded.                  
                  apply (f_apply dlog) in Ded; simpl.
                  rewrite E_com  in Ded.
                  apply mult_inv_l in Ded.
                  clear H H2 Heal I. (* speeds up smt *)
                  fresh Ded; clear Ded.
                  +++ smt ~prover:CVC5 ~no_macros.
                  +++ auto.
                  +++ intro [_ [[_ | _] _]]. smt ~prover:CVC5 ~no_macros. smt ~prover:CVC5 ~no_macros.
                  +++ intro [_ [[_ | _] _]]. smt ~prover:CVC5 ~no_macros. smt ~prover:CVC5 ~no_macros.
                  +++ smt ~prover:CVC5 ~no_macros.

               ++ have U := PIR_R (ind_pred i, true) _ _. 
                  rewrite /pair_init. smt ~no_macros. 
                  rewrite /getR /=. smt ~no_macros. 
                  intro R I. clear R H H2.
                  apply (f_apply fst) in I. simpl.      
                  rewrite /stR /getR /= in U.
                  smt ~no_macros. (* i <> ind_zero *)

               ++ intro i0 I. (* RKRreceive <> RKIreceive *)
                  have I0 : I i0 < R i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                  clear I.
                  have S := NoColRKRreceiveRKIreceive (R i) (I i0) _. constraints.
                  intro T.  apply (f_apply fst) in T.  simpl. rewrite T neq_irrefl in S. assumption.
               }

             + (* second prf subgoal: equality test is deducible. *)
               rewrite -expand_ORKRreceive.



               have HF := DeduceFrame  (pred (R i)) (pred (R i)) _;
                 [1:constraints].
               rewrite /( |> ) in HF; destruct HF as [fF HF].

               have HOstRR := (bigger_ORKRreceive (R i) (pred (R i))) _ ;
                  [1:constraints].
               rewrite /( |> ) in HOstRR; destruct HOstRR as [fOstRR HOstRR].
               have HOstIR := (bigger_ORKIreceive (R i) (pred (R i))) _ ;
                  [1:constraints].
               rewrite /( |> ) in HOstIR; destruct HOstIR as [fOstIR HOstIR].
 
               rewrite /gI /input.
               rewrite /OddhR. simpl.
               rewrite /( |> ).
               rewrite /Oracles /Opublic in HF.

               ghave [H3 | H3] : 
                 [(not (SyncIR (ind_pred i))) 
                      ||  (SyncIR (ind_pred i)) ]; 1: rewrite -impl_charac; intro _; assumption.


              (* we rely on not SyncIR (ind_pred i) *)
              ++  exists
                    (fun (x:(_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_)) =>
                      (fun (y:message) =>
                         (fst y = (x#5) i) &&
                         ofG (toG (snd y)) = (snd y) &&
                         ((x#10) (toG (snd y)) (toG ((att (fF (x#1,x#2,x#17,fOstIR (x#3),x#4,fOstRR (x#5),(x#6,x#7,x#8,x#9,x#10,x#11,x#12,x#13,x#14),x#15,x#16))))) i)
                      )
                    ).
                  simpl.
                  rewrite /ORKRreceive /= if_true /= ; [1:auto].

                  rewrite fun_eq /=.
                  intro x.
                  rewrite pair_eq.
                  rewrite HOstRR HOstIR HF /=.

                  rewrite eq_iff; split.
                  --+ intro [Eq1 Eq2 Eq3].
                      rewrite Eq1 eq_refl_e. by simpl.
                  --+ intro [_ He]. by rewrite He. 

                 
               ++ (* case SyncIR (i-1) && not HealthyI (i-1) *)
                   simpl.
                   rewrite H3 /= in H2.
                  ghave [H4 | H4] : [i = ind_one || ind_one ~< i] by smt  ~no_macros.                
                  +++ rewrite H4 /=.
                      have _ : false.
                      localize H2 as H0.
                      rewrite H4 in H0.
                      
                      rewrite -healthyI_to_HealthyI /healthyI  safeI_zero in H0.
                      smt. 
                      by simpl.

                  +++ 
                      have HRHR : syncIR (ind_pred i) by rewrite syncIR_to_SyncIR.
    
                      have Heq' := SyncIR (ind_pred i) _ ; [1:smt  ~no_macros ].
                      rewrite syncIR_to_SyncIR in Heq'.
                      have Heq := Heq' _; [1: auto].
                      clear Heq'.
                      rewrite /= in Heq.
    
                      have Hi := ind_succ_pred i _; [1: smt  ~no_macros].
                      rewrite Hi /= in Heq.
                      rewrite Heq.
                      
                      have _ : I (ind_pred i) < R i. 
                        { rewrite /syncIR Hi /= in HRHR.
                          smt  ~no_macros. }
    
                      exists
                        (fun (x:(_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_)) =>
                          (fun (y:message) =>
                             (fst y = (x#4) (ind_pred i)) &&
                             ofG (toG (snd y)) = (snd y) &&
                             ((x#10) (toG (snd y)) (toG ( (att (fF (x#1,x#2,x#17,fOstIR (x#3),x#4,fOstRR (x#5),(x#6,x#7,x#8,x#9,x#10,x#11,x#12,x#13,x#14),x#15,x#16))))) i)
                          )
                        ).
                      
                      rewrite /ORKIsend /= if_true /=; [1:auto].
    
                      rewrite fun_eq /=.
                      intro x.
                      rewrite pair_eq.
                      rewrite HOstRR HOstIR HF /=.
    
                      rewrite eq_iff; split.
                      --+ intro [Eq1 Eq2 Eq3].
                          rewrite Eq1 eq_refl_e. by simpl.
                      --+ intro [_ He]. by rewrite He. 
    

           + have ZIH := HP taur side _; [1:auto].
             rewrite /Secret_prop /Secret_target in ZIH.
             have DedNIH := ZIH _ n n2 _; [1,2:constraints].

	     rewrite -expand_rhs; [1:constraints].
             rewrite -expand_ORKRreceive. 
             rewrite /Oracles /Opublic Htau in DedNIH.
             by apply DedNIH.



**  rewrite H /=.
    have ZIH := HP taur side  _; [1:auto].
    rewrite /Secret_prop /Secret_target in ZIH.
    have DedNIH := ZIH _ n n2 _; [1,2:constraints].
    rewrite /Oracles Htau in DedNIH.
    by apply DedNIH.


  (**********************************)
  (* Case 2.2: tau0=I i is maximum *)
  (**********************************)   
    (* Here, we have to scale ORKIsend one step back. *)
    (* If HealthyI i, this is trival. *)
    (* Otherwise, the attacker gets an extra RKIsend from ORKIsend when not(HealthyI i) 

      We do the following case disjunction, where we use prf to get
      ride of the hash, but either because some inputs of the hash are
      secret, or because we get a fresh hash for which we can already
      test equlity.

syncRI i    HealthyR i
  true          true         -> RKIreceive@I i =RKRsend@R i which is secret, call prf.
  false           X          -> RKIreceive@I i is public from ORKIreceive, call prf ~equality
  true          false        -> RKIreceive@R i =RKRsend@R (i) is public from ORKRsend call prf ~equality

                    *)

   * (* first, we isolate the value added to ORKRsend, the rest does not change. *)
     rewrite Htau /Oracles.
     deduce with (ORKIsend_split i); [1: constraints].  
     rewrite stable_ORKRsend; [1: constraints].


     (* Depending on HealthyI i, either RKIsend@I i or nothing is added *)
     ghave [H|H] : [ not(HealthyI i) || (HealthyI i)]; 1: rewrite -impl_charac; intro _; assumption.

     (* Case not HealthyI i:
        this is the case where we must remove an RKIsend *)
     ** rewrite H /RKIsend /=. 
        rewrite /gSendI  => //.
        

	rewrite expand_rhs; [1:constraints].	     
        rewrite expand_ORKIreceive.

        rewrite /Opublic.

        (* depending on whether SyncRI (i) and HealthyR (i) hold, the reason
           why prf can be applied changes -- see comment at the beginning of case 2. *)
        ghave [H2|H3] :
          [ ( (HealthyI  (ind_pred i) && not(SyncRI i)) || (SyncRI i && HealthyR i) )
          || not( ( (HealthyI  (ind_pred i) && not(SyncRI i))) || (SyncRI i && HealthyR i) )]
	 ;  1: rewrite or_comm -impl_charac; intro _; assumption.

        
         (* case SyncRI (i) && HealthyR (i): RKIreceive@I i = RKRsend@R (i) is secret *)
         *** prf ~left ~under_hash 17.
           + { (* first subgoal: phi_prf *)
               repeat split.
               ++ have Neq := NoColRKIsendRKIreceive (pred (I i)) (I i) _; 1:constraints.
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro i0 _ _.
                  have Neq := NoColRKIsendRKIreceive (pred (I i0)) (I i) _; 1:constraints.
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq in Neq; by simpl.
               ++ have Neq := PIR_I ( i, false). 
                  rewrite /getI /pair_init /stI /getI /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)
               ++ intro j _ _ Eq. 
                  have U : RKRreceive@R j = RKIsend@I i. 
                  by rewrite /RKIsend /RKRreceive Eq /=.
                  by have _ := NoColRThenI i j _; [1:constraints].
               ++ intro j _ _ Eq.  
                  have U : RKRreceive@R j = RKIreceive@I i. 
	          apply (f_apply fst) in Eq. rewrite /= in Eq.
                  by rewrite /RKRreceive Eq /=.
                  by have S := NoColRKRreceiveRKIreceive (R j) (I i) _; [1:constraints].
               ++ intro j _ _ _ Eq.
                  have Neq := NoColRKIsendRKIreceive (pred (I j)) (I i) _; [1:constraints].
                  apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j _ _ _ Eq.  
                  localize Htaur as C.
                  case C.
                   +++ have Neq := NoColRKIreceive i j _ _; [1,2: constraints]. 
                       apply (f_apply fst) in Eq; simpl; rewrite Eq /RKIreceive neq_irrefl in Neq. assumption.
                   +++ smt ~no_macros.

               ++ have Neq := PIR_I ( i, false). 
                  rewrite /getI /pair_init /stI /getI /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)
               ++ intro j _ _ _ T Eq. 
                  have U : RKIsend@I i = RKRreceive@R j.
                  by rewrite /RKIsend /RKRreceive Eq /=.
                  have Neq := NoColRThenI i j _; [1:constraints].
                  by rewrite U /= neq_irrefl in Neq. 

               ++ intro j _ _ _ _ _.
                  have Neq := NoColRKIsendRKIreceive (pred (I j)) (I i) _ ; [1:constraints]. 
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j I.
                  have I0 : RO j < I i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); 
                     try constraints.
                   }
                  intro Ded.      
                  apply (f_apply snd) in Ded. simpl.
                  rewrite /gR in Ded.
                  apply (f_apply toG) in Ded. simpl.
                  apply (f_apply dlog) in Ded. simpl.
                  rewrite E_com  in Ded.
                  apply mult_inv_l in Ded.
                  clear   Heal I H2 H.
                  fresh Ded.
                  +++ smt  ~no_macros. 
                  +++ smt  ~no_macros. 
                  +++ smt  ~no_macros. 
                  +++ smt ~no_macros.   
                  +++ smt ~no_macros. 



               ++ intro j I. 
                  have I0 : R j < I i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                     constraints.
                   }
                  intro Ded.
                  apply (f_apply snd) in Ded; simpl.
                  rewrite /gR in Ded.                  
                  apply (f_apply dlog) in Ded; simpl.
                  rewrite E_com  in Ded.
                  apply mult_inv_l in Ded.
                  clear H H2 Heal I. (* speeds up smt *)
                  fresh Ded; clear Ded.
                  +++ smt ~no_macros.  
                  +++ smt ~no_macros. 
                  +++ intro [_ [[_ | _] _]]. smt ~no_macros.  smt ~no_macros. 
                  +++ smt ~no_macros. 
                  +++ smt ~no_macros. 


               ++ intro i0 I. (* RKRreceive <> RKIreceive *)
                  have I0 : R i0 < I i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                  clear I.
                  have S := NoColRKRreceiveRKIreceive (R i0) (I i) _. constraints.
                  intro T.  apply (f_apply fst) in T.  simpl. 
		  rewrite T neq_irrefl in S; assumption.


               ++ intro j I. (* sIRReceive <> RKIsend *)
                  have I0 : I j < I i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
		  clear I.
                  have Neq := NoColRKIsendRKIreceive (pred (I j)) (I i) _. constraints.
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.

               ++ have Neq := PIR_I ( i, false). 
                  rewrite /getI /pair_init /stI /getI /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)

               ++ intro j I. (* RKIreceive <> RKIreceive *)
                  have I0 : I j < I i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                  clear I.
                  have Neq := NoColRKIreceive i j _ _; 1,2: constraints. 
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.

             }

           + (* second prf subgoal: the hashed message cannot be deduced *)
             (* use secrecy of RKRreceive that comes from syncIR (i-1)
               (which implies RKRreceive@R i =RKIsend@I (i-1))
               and HealthyI (i-1) *)
            
             ghave Neq : [i <> ind_zero]. smt ~no_macros. 


             apply (ded_right fst).
             simpl.

             rewrite -expand_ORKIreceive. 


             case H2.
             ++ 
                have ZIH := (HP (I ( i))) 1 _; [1:by simpl].
                rewrite /Secret_prop /Secret_target /Oracles Htau /Opublic in ZIH.
                have DedNIH := ZIH _ n n2 _; [1,2:auto]; clear ZIH.
	        apply if_false_ded in DedNIH; [1: auto]. 
	        apply if_false_ded in DedNIH; [1: auto]. 
	        apply if_false_ded in DedNIH; [1: auto]. 
	        apply if_true_ded in DedNIH; [1: auto]. 

                by apply DedNIH.
             ++ 
               rewrite SyncRI.  { localize H2 as H1. by rewrite -syncRI_to_SyncRI in H1. }
               auto.  
               ghave Ord : [R i < I i]. { localize H2 as H1. by rewrite -syncRI_to_SyncRI /syncRI in H1. }
  
                  
                  have ZIH := (HP (R ( i))) 4 _; [1:auto].
                  rewrite /Secret_prop /Secret_target in ZIH.
                  have DedNIH := ZIH _ n n2 _; [1,2:auto]; clear ZIH.
                  rewrite /= Htau /Oracles /Opublic /ORKRreceive /RKRreceive in DedNIH.
                  by apply DedNIH.

 
           + have ZIH := HP taur side _; [1:auto].
             rewrite /Secret_prop /Secret_target in ZIH.
             have DedNIH := ZIH _ n n2 _; [1,2:constraints].
             rewrite -expand_ORKIreceive -expand_rhs. constraints.
             rewrite /Oracles /Opublic Htau in DedNIH. 
             by apply DedNIH.

         (* case not SyncRI (i) || not HealthyR (i):
             the equality test is deducible, since
             - DH eq test comes from gdh oracles
             - RKRreceive@R i is leaked:
                -> either not SyncRI (i), and then OStIReceive leaks it
                -> or SyncRI (i) && not HealthyR (i), and then stRIeceive = RKRsend which is leaked
                                                         by OStRSend. *)
         *** 
             prf ~left ~equality 17.
             + { (* first subgoal: phi_prf *)
                 repeat split.
               ++ intro i0 _ _.
                  have Neq := NoColRKIsendRKIreceive (pred (I i0)) (I i) _; 1:constraints.
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq in Neq; by simpl.
               ++ have Neq := PIR_I ( i, false). 
                  rewrite /getI /pair_init /stI /getI /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)
               ++ intro j _ _ Eq. 
                  have U : RKRreceive@R j = RKIsend@I i. 
                  by rewrite /RKIsend /RKRreceive Eq /=.
                  by have _ := NoColRThenI i j _; [1:constraints].
               ++ intro j _ _ Eq.  
                  have U : RKRreceive@R j = RKIreceive@I i. 
	          apply (f_apply fst) in Eq. rewrite /= in Eq.
                  by rewrite /RKRreceive Eq /=.
                  by have S := NoColRKRreceiveRKIreceive (R j) (I i) _; [1:constraints].
               ++ intro j _ _ _ Eq.
                  have Neq := NoColRKIsendRKIreceive (pred (I j)) (I i) _; [1:constraints].
                  apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.
               ++ intro j _ _ _ Eq.  
                  localize Htaur as C.
                  case C.
                   +++ have Neq := NoColRKIreceive i j _ _; [1,2: constraints]. 
                       apply (f_apply fst) in Eq; simpl; rewrite Eq /RKIreceive neq_irrefl in Neq. assumption.
                   +++ smt ~no_macros.


               ++ have Neq := PIR_I ( i, false). 
                  rewrite /getI /pair_init /stI /getI /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)

               ++ intro j _ _ _ T Eq. 
                  have U : RKIsend@I i = RKRreceive@R j.
                  by rewrite /RKIsend /RKRreceive Eq /=.
                  have Neq := NoColRThenI i j _; [1:constraints].
                  by rewrite U /= neq_irrefl in Neq. 

               ++ intro j _ _ _ _ _.
                  have Neq := NoColRKIsendRKIreceive (pred (I j)) (I i) _ ; [1:constraints]. 
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.

               ++ intro j I.
                  have I0 : RO j < I i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); 
                     try constraints.
                   }
                  intro Ded.      
                  apply (f_apply snd) in Ded. simpl.
                  rewrite /gR in Ded.
                  apply (f_apply toG) in Ded. simpl.
                  apply (f_apply dlog) in Ded. simpl.
                  rewrite E_com  in Ded.
                  apply mult_inv_l in Ded.
                  clear   Heal I  H.
                  fresh Ded.
                  +++ smt  ~no_macros. 
                  +++ smt  ~no_macros. 
                  +++ smt  ~no_macros. 
                  +++ smt ~no_macros.   
                  +++ smt ~no_macros. 



               ++ intro j I. 
                  have I0 : R j < I i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                     constraints.
                   }
                  intro Ded.
                  apply (f_apply snd) in Ded; simpl.
                  rewrite /gR in Ded.                  
                  apply (f_apply dlog) in Ded; simpl.
                  rewrite E_com  in Ded.
                  apply mult_inv_l in Ded.
                  clear H Heal I. (* speeds up smt *)
                  fresh Ded; clear Ded.
                  +++ smt ~no_macros.  
                  +++ smt ~no_macros. 
                  +++ intro [_ [[_ | _] _]]. smt ~no_macros.  smt ~no_macros. 
                  +++ smt ~no_macros. 
                  +++ smt ~no_macros. 


               ++ intro i0 I. (* RKRreceive <> RKIreceive *)
                  have I0 : R i0 < I i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                  clear I.
                  have S := NoColRKRreceiveRKIreceive (R i0) (I i) _. constraints.
                  intro T.  apply (f_apply fst) in T.  simpl. 
		  rewrite T neq_irrefl in S; assumption.


               ++ intro j I. (* sIRReceive <> RKIsend *)
                  have I0 : I j < I i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
		  clear I.
                  have Neq := NoColRKIsendRKIreceive (pred (I j)) (I i) _. constraints.
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.

               ++ have Neq := PIR_I ( i, false). 
                  rewrite /getI /pair_init /stI /getI /= in Neq.
                  smt ~no_macros. (* i <> ind_zero *)

               ++ intro j I. (* RKIreceive <> RKIreceive *)
                  have I0 : I j < I i.
                   { rewrite Htau in *.
                     repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                     try constraints.
                   }
                  clear I.
                  have Neq := NoColRKIreceive i j _ _; 1,2: constraints. 
                  intro Eq; apply (f_apply fst) in Eq; simpl; rewrite Eq neq_irrefl in Neq; assumption.


               }

             + (* second prf subgoal: equality test is deducible. *)
               rewrite -expand_ORKIreceive. 
               have HF := DeduceFrame  (pred (I i)) (pred (I i)) _;
                 [1:constraints].
               rewrite /( |> ) in HF; destruct HF as [fF HF].

               have HOstIR := (bigger_ORKIreceive (I i) (pred (I i))) _ ;
                  [1:constraints].
               rewrite /( |> ) in HOstIR; destruct HOstIR as [fOstIR HOstIR].
               have HOstRR := (bigger_ORKRreceive (I i) (pred (I i))) _ ;
                  [1:constraints].
               rewrite /( |> ) in HOstRR; destruct HOstRR as [fOstRR HOstRR].
               rewrite /gR /input.
               rewrite /OddhI. simpl.
               rewrite /( |> ).
               rewrite /Oracles /Opublic in HF.

               ghave [H2 | H2] : 
                 [not (SyncRI (i)) || (SyncRI (i))]; 1: rewrite -impl_charac; intro _; assumption.


               ++ (* case not SyncIR ( i) *)
                   rewrite H2 /= in H3. 
                  exists
                    (fun (x:(_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_)) =>
                      (fun (y:message) =>
                         (fst y = (x#4) i) &&
                         ofG (toG (snd y)) = (snd y) &&
                         ((x#11) (toG (snd y)) (toG ((att (fF (x#1,x#2, x#3, fOstIR (x#4),x#17,fOstRR (x#5),(x#6,x#7,x#8,x#9,x#10,x#11,x#12,x#13,x#14),x#15,x#16))))) i)
                      )
                    ).

                  rewrite /ORKIreceive /= if_true /=; [1:auto].

                  rewrite fun_eq /=.
                  intro x.
                  rewrite pair_eq.
                  rewrite HOstIR HOstRR  HF /=.

                  rewrite eq_iff; split.
                  --+ intro [Eq1 Eq2 Eq3].
                      rewrite Eq1 eq_refl_e. by simpl.
                  --+ intro [_ He]. by rewrite He.  


                 
               ++ (* case SyncRI (i) && not HealthyR (i) *)
                  rewrite H2 /= in H3. 

            
                 rewrite SyncRI. { localize H2 as H1. by rewrite -syncRI_to_SyncRI in H1. }
                 auto.  
                 ghave Neq : [i <> ind_zero]. smt ~no_macros. 
                 ghave Ord : [R i < I i]. { localize H2 as H1. by rewrite -syncRI_to_SyncRI /syncRI in H1. }
    

                  exists
                    (fun (x:(_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_)) =>
                      (fun (y:message) =>
                         (fst y = (x#3) (i)) &&
                         ofG (toG (snd y)) = (snd y) &&
                         ((x#11) (toG (snd y)) (toG ( (att (fF (x#1,x#2,x#3 ,fOstIR (x#4),x#17,fOstRR (x#5),(x#6,x#7,x#8,x#9,x#10,x#11,x#12,x#13,x#14),x#15,x#16))))) i)
                      )
                    ).
                  
                  rewrite /ORKRsend /= if_true /=; [1:auto].

                  rewrite fun_eq /=.
                  intro x.
                  rewrite pair_eq.
                  rewrite HOstRR HOstIR HF /=.

                  rewrite eq_iff; split.
                  --+ intro [Eq1 Eq2 Eq3].
                      rewrite Eq1 eq_refl_e. by simpl.
                  --+ intro [_ He]. by rewrite He. 


           + have ZIH := HP taur side _; [1:auto].
             rewrite /Secret_prop /Secret_target in ZIH.
             have DedNIH := ZIH _ n n2 _; [1,2:constraints].

             rewrite -expand_ORKIreceive -expand_rhs. constraints.
             rewrite /Oracles /Opublic Htau in DedNIH.
             by apply DedNIH.


**  rewrite H /=.
    have ZIH := HP taur side _; [1:auto].
    rewrite /Secret_prop /Secret_target in ZIH.
    have DedNIH := ZIH _ n n2 _; [1,2:constraints].
    rewrite /Oracles Htau in DedNIH.
    by apply DedNIH.


  (************************************)
  (* Case 2.3: tau0<>R/I i is maximum *)
  (************************************)
  * simpl.
    rewrite /Oracles.
    rewrite stable_ORKRsend.  intro i T.  by have _ := Zt i.  (* scale Oh' one step back *)
    rewrite stable_ORKIsend.  intro i T.  by have _ := Zt i.  (* scale Oh' one step back *)
    have ZIH := HP taur side _; [1:auto].
    rewrite /Secret_prop /Secret_target in ZIH.
    have DedNIH := ZIH _ n n2 _; [1,2:constraints].
    rewrite /Oracles in DedNIH.
    by apply DedNIH.
Qed.

