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
include[admit] "secrecy_p2.sp".

name dummy_secret : message.

(**********************************************)
(* Case 4: ORKIreceive/ORKRreceive is maximum *)
(**********************************************)	

(* Simplification : The trace alternate R and I and maximal tau is R

              Rlice                     Iob
-----------------------------------------------------------
                r1*          c1* <--h'-- r1?*
                |                        |
                |h                       |h
                V                        V
                r2?* --h'--> c2*         r2*
                |                        |   tau1l < tau3l
............... |h ......                |h  taur < tau3l
                V        .               V
                r3!       .  c3* <--h'-- r3?*
max tau3l       |          .             |
tau2l <= tau3L  |h          ............ |h ...............
                V                        V
                r4* --h'--> c4           r4
*)
(* We will have to eliminate the extra hash h produced by ORKIreceive or
ORKRreceive on the right hand side. *)

global lemma Secret_case4 @set:S/left (tau0:timestamp[const]):
  [init < tau0]
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur < tau0] ->
      (Secret_prop t (pred tau0) (pred tau0) (pred tau0) (pred tau0) taur))
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur < tau0] ->
      (Secret_prop t (pred tau0) (pred tau0) tau0 (pred tau0) taur)).
Proof.
  intro HI HP taur side Htaur.
  rewrite /Secret_prop /Secret_target /=.
  intro Hhap n n2 Heal.


  ghave [[i Htau] | [i Htau] | Zt] :
       (Exists (i:index [const]), [tau0=R i]) 
    \/ (Exists (i:index [const]), [tau0=I i]) 
    \/ (Forall (i:index [const]), [tau0<>R i && tau0<>I i ]).

   * case tau0; try (   (intro [j R] + intro j); right; right; intro j'; constraints ).  
     intro [i R]. left. by exists i.
     intro [i I]. right. left. by exists i.


  (*********************************)
  (* Case 4.1: tau0=R i is maximum *)
  (*********************************)
  

   * rewrite  Htau /Oracles.
     deduce with (ORKRreceive_split i). auto.
     rewrite stable_ORKIreceive.  intro j T.  constraints. 

    ghave [H1|H1] : [not((not (SyncIR (ind_pred i)) && not (HealthyR (ind_pred i)))) || ((not (SyncIR (ind_pred i)) && not (HealthyR (ind_pred i))))]
	; 1: rewrite -impl_charac; intro _; assumption.  

       (* direct induction case *)
    ** rewrite if_false. by simpl. 

       have ZIH := HP taur side _; [1:auto].
       rewrite /Secret_prop /Secret_target in ZIH.
       have DedNIH := ZIH _ n n2 _; [1,2:constraints].
       rewrite /Oracles Htau in DedNIH.
       by apply DedNIH.   
 
    ** rewrite if_true. by simpl.  
       rewrite /RKRreceive. 
       
        (* Here, we will apply prf ~equality, because we are in an
               unhealthy and unsynced case.  However, an issue is that
               the attacker may already have submitted this hash value
               in the past to the ROM action. We thus have to rewrite
               the hash, showing that if the attacker was already able
               to compute this value, the hash is useless.  *)

           have Ded1 :=  (ORKRsend_pred i) _ _; 1,2: constraints. 
           ghave Ded : $( 
                          ( fun t => if t <= pred(R i) then input@t ,
          	            fun t => if t <= pred(R i) then output@t ,
                           (fun x : message => x =    <RKRsend@pred (R(i)),ofG (gRecR@R(i))>),
         	            h (
         	            if (exists (x:index),
         	             (fun (y:index) =>
                               RO(y) < R(i) &&
                               input@RO(y) = <RKRsend@pred (R(i)),ofG (gRecR@R(i))>)
                               x) 
                             then
         	              dummy_secret
         	            else
                               <RKRsend@pred (R(i)),ofG (gRecR@R(i))>          
                            , k)
                            , dummy_secret)
                            |>
         	            (h (<RKRsend@pred (R(i)),ofG (gRecR@R(i))>, k))
             ).
           {
             rewrite /( |>).
             exists (fun x : _*_*_*_*_ => 
                      try find j such that RO j < R i && (x#3) (( (x#1) (RO j))) in  (x#2) (RO j)
                                     else x#4).
             simpl. rewrite if_true; 1: constraints. rewrite if_true; 1: constraints.
             rewrite try_carac_1.      
             case (exists (x:index),
              (fun (y:index) =>
                 RO(y) < R(i) &&
                 input@RO(y) = <RKRsend@pred (R(i)),ofG (gRecR@R(i))>)
                x) . 
             + intro C.   rewrite if_true //. 
               destruct C.
               have U := choose_spec (fun (y:index) =>
               RO(y) < R(i) &&
       
               input@RO(y) = <RKRsend@pred (R(i)),ofG (gRecR@R(i))>) x _.  auto. 
               simpl.
               destruct U as [Ord Eq].
               expand ~def output.
               rewrite if_true.   

               have dum : forall (t,t':timestamp), t < t' => happens(t) by constraints.
               by apply (dum _ (R i)). 
       
       
               by rewrite Eq.
             
             + intro U. rewrite if_false //.   by rewrite if_false //.
           }
           deduce with Ded => {Ded}.
        

        
           rewrite /Opublic. 
                 
        
           have C : (exists (x:index),
                    (fun (y:index) =>
                       RO(y) < R(i) &&
                       input@RO(y) = <RKRsend@pred (R(i)),ofG (gRecR@R(i))>)
                      x) || not (exists (x:index),
                    (fun (y:index) =>
                       RO(y) < R(i) &&
                       input@RO(y) = <RKRsend@pred (R(i)),ofG (gRecR@R(i))>)
                      x). 
               {
              case (exists (x:index),
              (fun (y:index) =>
              RO(y) < R(i) && input@RO(y) = <RKRsend@pred (R(i)),ofG (gRecR@R(i))>)
             x). by intro U; left. by intro U; right.
              }
            


           prf ~left ~under_hash ~equality 20.
           + { (* first subgoal: phi_prf *)
               (repeat split);  try localize C as Ce => {C}; 
                                case Ce; [1: try (intro j Ord; 
                                             rewrite if_true; [2: intro E; by fresh E | 1:assumption])].
               ++ rewrite if_true; 1:assumption. intro Eq. by fresh Eq.
               ++ rewrite if_false; 1:assumption. 
       	            clear  Ce.
      	            have O : i <> ind_zero. smt ~no_macros. 
      	            rewrite RKRsend_pred. auto.
                    case i=ind_one. 
                    +++ intro Eq. localize H1 as H1'. rewrite -healthyR_to_HealthyR in H1'. smt.
                    +++  intro Neq. rewrite if_false //. 
      		         have R := PIR_R (ind_pred i, false) _.
                         smt. 
                         smt.
               ++ intro j I. 
                  have I0 : RO j < R i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); 
                     try constraints.
                   }
                 rewrite if_false; 1:assumption. 
                 rewrite not_exists_1 in Ce. 
                 have Neg := Ce j. simpl. intro Eq. rewrite Eq I0 in Neg. simpl. assumption. 
               ++   intro j I. rewrite if_false; 1:assumption => {Ce Heal}. 
                        have I0 : R j < R i.
                         { rewrite Htau in *.
                           repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                           try constraints.
                         }
                      clear I.
                      have _ := NoColRKRreceive i j _ _; 1,2: constraints.  by simpl. 
   	       ++ intro j I. rewrite if_false; 1:assumption => {Ce Heal}. 
                        have I0 : R j < R i.
                         { rewrite Htau in *.
                           repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                           try constraints.
                         }
                  have _ := NoColRKRsendRKRreceive (pred (R i)) (R j) _; 1:constraints. 
		  clear I.    
                  by simpl.      
               ++   intro j I. rewrite if_false; 1:assumption => {Ce Heal}. 
      	              have I0 : I j < R i. 
                     { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                       constraints.
                     }
                   have _ := NoColRKRsendRKIsend (pred (R i)) (pred (I j)) _; 1:constraints.  
                   clear I.
                   by simpl.
      
               ++   intro Ord. 
                    rewrite if_true; 1:assumption => {Ce Heal}. 
                    intro Eq. by fresh Eq.
      
               ++   intro Ord. rewrite if_false; 1:assumption => {Ce Heal Ord}. 
      	            have O : i <> ind_zero. smt ~no_macros. 
      	            rewrite RKRsend_pred. auto.
                    case i=ind_one. 
                    +++ intro Eq. localize H1 as H'. rewrite -healthyR_to_HealthyR in H'. smt.
                    +++  intro Neq. rewrite if_false //. 
      		         have R := PIR_R (ind_pred i, false) _.
                         smt.
                         smt. 
     
               ++   intro j I. 
      	              have I0 : I j < R i. 
                     { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                       constraints.
                     }
		      rewrite if_false; 1:assumption => {Ce Heal}. 
    
                     intro Eq. clear  I.
                     have Eq2 : RKRreceive@R i = RKIsend@I j by auto.
                     have R  := NoColRI (ind_pred i, true) (j, true) _ _.
                     +++  intro Eqij. simpl.
                          localize H1 as R. 
                          
                           have U := NoColRIsync (ind_pred i, true) _ _. 
                             {
                              rewrite /sync. simpl. by rewrite syncIR_to_SyncIR.
                              }
                            rewrite /getR /getI /=. smt ~no_macros.             
                            rewrite /stR /stI /getR /getI /= in U.                              
                            smt ~no_macros.
                     +++ rewrite /getR /getI /=. smt ~no_macros.             
                     +++ rewrite /stR /stI /getR /getI /= in R. smt ~no_macros. 
        
    
             }
           + rewrite /( |>).   simpl.

             exists (fun f : _*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_ =>
            (fun x:message =>
             try find j such that RO j < R i && (f#20) ((f#18) (RO j)) in          
               (x= f#21)
	     else 
                (f#20) x)). 
  	     simpl.
             apply fun_ext. intro x /=.
             rewrite try_carac_1 /=. 
             smt ~no_macros. 
           + fresh 20. clear C.
             rewrite /gRecR.
	     rewrite /OddhR.

             ghave Ded : $(
                   (RKRsend@pred(R i), OddhR,
                     (fun (t:timestamp) => if (t <= pred (R(i))) then frame@t)
                    )
                  |>  (fun (x:message) =>
                 x = <RKRsend@pred (R(i)),ofG (gI@R(i) ^ skR (ind_pred i))>) ).
             {
              rewrite /( |>). rewrite /OddhR. rewrite /gI /input.
              exists (fun f : _*_*_ => 
                      (fun (x:message) => fst(x) = f#1 &&                                                  ofG (toG (snd x)) = (snd x) &&
                         (f#2) (toG (snd x)) 
                      ( (toG ( (att ((f#3) (pred (R i))))))) (ind_pred i))).
              simpl. rewrite if_true //. 
	      rewrite fun_eq /=.
              intro x.
              rewrite pair_eq. rewrite eq_iff; split.
              ++ intro [R I]. by simpl. 
              ++ intro [R I]. by rewrite I. 
             }
             
             deduce with Ded => {Ded}.
             deduce with Ded1 => {Ded1}.

             deduce with DeduceOutputNoConst (pred(R i)) (pred(R i)) _. 
             by simpl.

             deduce with DeduceInputNoConst (pred(R i)) (pred(R i)) _. 
             by simpl.

             deduce with  DeduceFrameNoConst (pred(R i)) (pred(R i)) _. 
             by simpl.

             have ZIH := HP taur side _; [1:auto].
             rewrite /Secret_prop /Secret_target in ZIH.
             have DedNIH := ZIH _ n n2 _; [1,2:by simpl].
             rewrite /Oracles /Opublic Htau in DedNIH.
             by apply DedNIH.
             
  (*********************************)
  (* Case 4.2: tau0=I i is maximum *)
  (*********************************)
   * rewrite  Htau /Oracles.
     deduce with (ORKIreceive_split i). auto.
     rewrite stable_ORKRreceive.  intro j T.  constraints. 
   
    ghave [H1|H1] : [not( (not (SyncRI i) && not (HealthyI (ind_pred i))) ) ||
 ( (not (SyncRI i) && not (HealthyI (ind_pred i))) )] => //. 
       (* direct induction case *)
    ** rewrite if_false. by simpl.  

       have ZIH := HP taur side _; [1:auto].
       rewrite /Secret_prop /Secret_target in ZIH.
       have DedNIH := ZIH _ n n2 _; [1,2:constraints].
       rewrite /Oracles Htau in DedNIH.
       by apply DedNIH.
   
    ** rewrite if_true.  by simpl.      
       rewrite /RKIreceive. 
       destruct H1 as [H1 H].  
           have Ded1 :=  (ORKIsend_pred i) _ H. constraints.
           ghave Ded : $( 
                          ( fun t => if t <= pred(I i) then input@t ,
          	            fun t => if t <= pred(I i) then output@t ,
                           (fun x : message => x =    <RKIsend@pred (I(i)),ofG (gRecI@I(i))>),
         	            h (
         	            if (exists (x:index),
         	             (fun (y:index) =>
                               RO(y) < I(i) &&
                               input@RO(y) = <RKIsend@pred (I(i)),ofG (gRecI@I(i))>)
                               x) 
                             then
         	              dummy_secret
         	            else
                               <RKIsend@pred (I(i)),ofG (gRecI@I(i))>          
                            , k)
                            , dummy_secret)
                            |>
         	            (h (<RKIsend@pred (I(i)),ofG (gRecI@I(i))>, k))
             ).
           {
             rewrite /( |>).
             exists (fun x : _*_*_*_*_ => 
                      try find j such that RO j < I i && (x#3) (( (x#1) (RO j))) in  (x#2) (RO j)
                                     else x#4).
             simpl. rewrite if_true //. rewrite if_true //. 
             rewrite try_carac_1.      
             case (exists (x:index),
              (fun (y:index) =>
                 RO(y) < I(i) &&
                 input@RO(y) = <RKIsend@pred (I(i)),ofG (gRecI@I(i))>)
                x) . 
             + intro C.   rewrite if_true //. 
               destruct C.
               have U := choose_spec (fun (y:index) =>
               RO(y) < I(i) &&
       
               input@RO(y) = <RKIsend@pred (I(i)),ofG (gRecI@I(i))>) x _. auto. 
               simpl.
               destruct U as [Ord Eq].
               expand ~def output.
               rewrite if_true.   

               have dum : forall (t,t':timestamp), t < t' => happens(t) by constraints.
               by apply (dum _ (I i)). 
       
       
               by rewrite Eq.
             
             + intro U. rewrite if_false //.   by rewrite if_false //.
           }
           deduce with Ded => {Ded}.
        

        
           rewrite /Opublic. 
                 
        
           have C : (exists (x:index),
                    (fun (y:index) =>
                       RO(y) < I(i) &&
                       input@RO(y) = <RKIsend@pred (I(i)),ofG (gRecI@I(i))>)
                      x) || not (exists (x:index),
                    (fun (y:index) =>
                       RO(y) < I(i) &&
                       input@RO(y) = <RKIsend@pred (I(i)),ofG (gRecI@I(i))>)
                      x). 
               {
              case (exists (x:index),
              (fun (y:index) =>
              RO(y) < I(i) && input@RO(y) = <RKIsend@pred (I(i)),ofG (gRecI@I(i))>)
             x). by intro U; left. by intro U; right.
              }
            
           prf ~left ~under_hash ~equality 20.
           + { (* first subgoal: phi_prf *)
               (repeat split);  try localize C as Ce => {C}; 
                                case Ce; [1: try (intro j Ord; 
                                             rewrite if_true; [2: intro E; by fresh E | 1:assumption])].

               ++ rewrite if_true; 1:assumption. intro Eq. fresh Eq.
               ++ rewrite if_false; 1:assumption => {Ce Heal}. 
      	          have O : i <> ind_zero. smt ~no_macros. 
  		  have R := PIR_I (ind_pred i, true) _ _.  smt. smt.
                  rewrite /stI /= /getI /= in R. 
      	          rewrite RKIsend_pred. auto. smt. 

               ++ intro j I. 
                  have I0 : RO j < I i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); 
                     try constraints.
                   }
		 rewrite if_false; 1:assumption => {Heal}.
                 rewrite not_exists_1 in Ce. 
                 have Neg := Ce j. simpl. intro Eq. rewrite Eq I0 in Neg. simpl. assumption. 

   	       ++ intro j I. rewrite if_false; 1:assumption => {Ce Heal}.
                  have I0 : R j < I i.
                  { rewrite Htau in *.
                    repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                    try constraints.
                  }
                  have _ := NoColRKRsendRKIsend (pred (R j)) (pred (I i)) _; 1:constraints.  
                  clear I. by simpl.
               ++ intro j I. 
      	          have I0 : R j < I i. 
                   { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                     constraints.
                   }
  		  rewrite if_false; 1:assumption => {Ce Heal}.
                  intro Eq. clear I.
                  have Eq2 : RKIreceive@I i = RKRsend@R j by auto.
                  have R  := NoColRI (j, false) (i, false) _ _.  
                  +++ intro Eqij. simpl.
                      localize H1 as R. 
                          
                       have U := NoColRIsync (i, false) _ _. 
                         {
                          rewrite /sync. simpl. by rewrite syncRI_to_SyncRI.
                          }
                        rewrite /getR /getI /=. smt ~no_macros.             
                        rewrite /stR /stI /getR /getI /= in U.                              
                        smt ~no_macros.
                 +++ rewrite /getR /getI /=. smt ~no_macros.             
                 +++ rewrite /stR /stI /getR /getI /= in R. smt ~no_macros. 
        

               ++ intro j I.
		  rewrite if_false; 1:assumption => {Ce Heal}.
                  have I0 : I j < I i.
                  { rewrite Htau in *.
                    repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                    try constraints.
                  }
                  have _ := NoColRKIreceive i j _ _; 1,2:constraints. 
                  clear I. by simpl.      

               ++ intro Ord. 
                  rewrite if_true; 1:assumption => {Ce Heal}. 
                  intro Eq. by fresh Eq.      

               ++ intro Ord. 
		  rewrite if_false; 1:assumption => {Ce Heal}.
       	          clear Ord.
      	          have O : i <> ind_zero. smt ~no_macros.
  		  have R := PIR_I (ind_pred i, true) _ _.  smt. smt.
                  rewrite /stI /= /getI /= in R. 
      	          rewrite RKIsend_pred. auto. smt.

               ++ intro j L.
		  rewrite if_false; 1:assumption => {Ce Heal}.
      	          have I0 : I j < I i. 
                  { repeat (destruct L as [[i1 _]|L] + destruct L as [_|L]);
                    constraints.
                  }
                  have _ := NoColRKIsendRKIreceive (pred (I i)) ((I j)) _; 1:constraints.                  
                  clear L. 
                  by simpl.
             }
           + rewrite /( |>).   simpl.
             exists (fun f : _*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_*_ =>
            (fun x:message =>
             try find j such that RO j < I i && (f#20) ((f#18) (RO j)) in          
               (x= f#21)
	     else 
                (f#20) x)). 
  	     simpl.
             apply fun_ext. intro x /=.
             rewrite try_carac_1 /=. 
             smt ~no_macros.    

           + fresh 20. clear C.
             rewrite /gRecI.
	     rewrite /OddhI.

             ghave Ded : $(
                   (RKIsend@pred(I i), OddhI,
                     (fun (t:timestamp) => if (t <= pred (I(i))) then frame@t)
                    )
                  |>  (fun (x:message) =>
                 x = <RKIsend@pred (I(i)),ofG (gR@I(i) ^ skI (ind_pred i))>) ).
             {
              rewrite /( |>). rewrite /OddhI. rewrite /gR /input.
              exists (fun f : _*_*_ => 
                      (fun (x:message) => fst(x) = f#1 &&                                                  ofG (toG (snd x)) = (snd x) &&
                         (f#2) (toG (snd x)) 
                      ( (toG ( (att ((f#3) (pred (I i))))))) (ind_pred i))).
              simpl. rewrite if_true //. 
	      rewrite fun_eq /=.
              intro x.
              rewrite pair_eq. rewrite eq_iff; split.
              ++ intro [R I]. by simpl. 
              ++ intro [R I]. by rewrite I. 
             }
             
             deduce with Ded => {Ded}.
             deduce with Ded1 => {Ded1}.

             deduce with DeduceOutputNoConst (pred(I i)) (pred(I i)) _. 
             by simpl.

             deduce with DeduceInputNoConst (pred(I i)) (pred(I i)) _. 
             by simpl.

             deduce with  DeduceFrameNoConst (pred(I i)) (pred(I i)) _. 
             by simpl.

             have ZIH := HP taur side _; [1:auto].
             rewrite /Secret_prop /Secret_target in ZIH.
             have DedNIH := ZIH _ n n2 _; [1,2:constraints].
             rewrite /Oracles /Opublic Htau in DedNIH.
             by apply DedNIH.
  (************************************)
  (* Case 4.3: tau0<>R/I i is maximum *)
  (************************************)

  * simpl.
    rewrite /Oracles.
    rewrite stable_ORKRreceive.  intro i T.  by have _ := Zt i.  (* scale Oh' one step back *)
    rewrite stable_ORKIreceive.  intro i T.  by have _ := Zt i.  (* scale Oh' one step back *)
    have ZIH := HP taur side _; [1:auto].
    rewrite /Secret_prop /Secret_target in ZIH.
    have DedNIH := ZIH _ n n2 _; [1,2:constraints].
    rewrite /Oracles in DedNIH.
    by apply DedNIH.
Qed.




(* Now put all four cases together for the inductive step *)
global lemma Secret_induction @set:S/left (tau0:timestamp[const]):
  [init < tau0]
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur <= pred tau0] ->
      (Secret_prop t (pred tau0) (pred tau0) (pred tau0) (pred tau0) taur))
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur <= tau0] ->
      (Secret_prop t tau0 tau0 tau0 tau0 taur)).


Proof.
  intro HI HP.
  apply Secret_case1 tau0 HI.
  apply Secret_case5 tau0 HI.


  apply Secret_case3_1 tau0 HI.  

  apply Secret_case2 tau0 HI.
  apply Secret_case3_2 tau0 HI.  



  apply Secret_case4 tau0 HI.
  (* now just some work to write pred instead of < *)
  intro taur t HII.
  by apply HP.
Qed.


 (* The lemma we want, by induction *)
global lemma Secret_before @set:S/left (tau0:timestamp[const]):
  [happens tau0] ->
   (Forall (taur:timestamp[const], t:int[const]), [taur <= tau0] ->
      (Secret_prop t tau0 tau0 tau0 tau0 taur)).
 Proof.
  induction @system:S/left tau0.
  intro tau0 HI _.
 
   ghave Htau : [tau0 = init || init < tau0] by constraints.
   case Htau.
     intro taur t Htaur.

     ghave Htaur' : [taur = init] by constraints.
     rewrite Htau Htaur' in * ; clear Htau Htaur' Htaur.
     apply Secret_init.
 
     apply Secret_induction tau0 Htau.
     by apply HI.  
 Qed.



(* The final theorem, works even when taur is higher *)
global lemma Secret_base @set:S/left (tau0, taur:timestamp[const], t:int[const]):
  [happens tau0 taur] ->
  Secret_prop t tau0 tau0 tau0 tau0 taur.
Proof.
  intro _.
  ghave Htaus : [taur <= tau0 || tau0 < taur] by constraints.
  case Htaus.

  + (* taur <= tau0: the previous lemma *)
    by apply Secret_before. 

  + (* tau0 < taur: previous lemma on taur, taur and they move the first taur back to tau0 *)
    have H := (Secret_before taur _ taur t _); [1,2:constraints].
    by apply (Secret_earlier taur tau0 taur tau0 taur tau0 taur).
Qed. 
