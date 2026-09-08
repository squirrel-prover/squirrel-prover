include Core.
include[admit] "indices.sp". 
include[admit] "DHLib.sp".
include[admit] "model.sp".
include[admit] "utils.sp".
include[admit] "trace.sp".
include[admit] "oracles.sp".

(* ------------------------------ *)

(**********************************)
(************* Oracles ************)
(**********************************)

global lemma deduce_stRCor @set:S/left (tau, tau' : timestamp[const]) :
  [tau <= tau'] ->
  $( (ORKRsend tau', Opublic)
  |> (stRCor@tau) ).
Proof.
  rewrite /ORKRsend in *.
  dependent induction @system:S/left tau ; intro tau IH I.
  case tau; intro Htau; try destruct Htau as [i Htau]; 
  rewrite /stRCor.
  + deduce.
  + have -> := firstIzero (pred Izero) _ => //. rewrite /stRCor. deduce.
  + rewrite Htau. 
    ghave [H |H] : [safeR i || safeR i=false]. 
    ++ by case safeR i.
    ++ rewrite H. simpl. by deduce.
    ++ 
       rewrite /Opublic. 
       rewrite /( |>).


       exists (fun x: _ * (_*_*_*_*_*_*_*_*_)=> <(x#1) i, ofE(((x#2)#7) i)>). simpl.
      rewrite -healthyR_to_HealthyR => //. 
      rewrite !H /= if_true.     
      simpl.         
      smt.
      by smt.
  + deduce with IH (pred tau) _ _; [1,2:auto].
  + deduce with IH (pred tau) _ _; [1,2:auto].
  + deduce with IH (pred tau) _ _; [1,2:auto].
  + deduce with IH (pred tau) _ _; [1,2:auto].
Qed.  

global lemma deduce_stICor @set:S/left (tau, tau' : timestamp[const]) :
  [tau <= tau'] ->
  $( (ORKIsend tau', Opublic)
  |> (stICor@tau) ).
Proof.
  rewrite /ORKIsend in *.
  dependent induction @system:S/left tau ; intro tau IH I.
  case tau; intro Htau; try destruct Htau as [i Htau]; 
  rewrite /stICor.
  + deduce.
  + have -> := firstIzero (pred Izero) _ => //. rewrite /stICor. deduce.
  + deduce with IH (pred tau) _ _; [1,2:auto].
  + rewrite Htau. 
    ghave [H |H] : [safeI i || safeI i=false]. 
    ++ by case safeI i.
    ++ rewrite H. simpl. by deduce.
    ++ 
       rewrite /( |>).
       exists (fun x: _ * (_*_*_*_*_*_*_*_*_)=> <(x#1) i, ofE(((x#2)#8) i)>). simpl.
      rewrite -healthyI_to_HealthyI => //. 
      rewrite !H /= if_true.     
      simpl.         
      smt.
      by smt.
  + deduce with IH (pred tau) _ _; [1,2:auto].
  + deduce with IH (pred tau) _ _; [1,2:auto].
  + deduce with IH (pred tau) _ _; [1,2:auto].
Qed.  

global lemma DeduceFrameNoConst @set:S/left (tau, tau' : timestamp [const]) :
 [tau <= tau'] ->
  $( (Oracles tau' tau' tau' tau') |> (fun t => if t<=tau then frame@t) ).
Proof.
  rewrite /Oracles.
  
  dependent induction @system:S/left tau ; intro tau IH' I.
  ghave [Ii | Ii] : [tau=init || tau <> init] by auto.
  + rewrite Ii.
    have -> : forall t, if (t <= init) then frame@t = if t=init then frame@init.
   {
   intro t. auto.
   }
  deduce.
 +
  have IH := IH' (pred tau) _ _ => // {IH'}.

 ghave Ded :
   $(  (fun (t:timestamp) => if (t <= pred tau) then frame@t
       , frame@tau)
       
   |>
   (fun (t:timestamp) => if (t <= tau) then frame@t)
  ).
  {
  rewrite /( |>).
  exists (fun x : _*_ => fun t => if t=tau then x#2 else (x#1) t).
  simpl.
  apply fun_ext.
  intro x /=.
  case x=tau. intro E.  rewrite if_true //. by rewrite if_true //.
               intro E.  rewrite if_false //.
               case (x <= tau) . intro E2.  by rewrite if_true //.
                                 intro Ne.  by rewrite if_false //.
  }

  deduce with Ded.


  case tau; intro Htau; try destruct Htau as [i Htau];
  have He := (is_exec tau _);[1:auto];
  rewrite /frame; [1: deduce];
   rewrite /output;  
  try rewrite He /=;
  try fa !<_,_>;
  deduce with IH.
  - have In := firstIzero (pred Izero) _ => //.

    rewrite /exec /cond  In /exec /=.
    rewrite /Opublic.  
    deduce.

  - rewrite /Opublic.  
    deduce. 
    rewrite /( |> ) in IH.    
    destruct IH as [fIH EIH].

    rewrite /( |> ).
    exists (fun (x :  _*_*_*_*_*_*(_*_*_*_*_*_*_*_*_)*_*_) => (
          (if SyncIR (ind_pred i) then 
              (if i=ind_one then ((x#7)#9)
	       else
              (if HealthyI (ind_pred i) then 
                       (x#2) (ind_pred i)  
              else  ((x#7)#2) ((x#5) (ind_pred i)))
	       )
         else 
             if HealthyR (ind_pred i) then
                (x#8) i
             else ((x#7)#2) ((x#6) i) )
              , 
          if HealthyR i then (x#1) i else ((x#7)#2) ((x#3) i)
)).
    rewrite /=.  
    rewrite /OCKRsend /OCKIsend /OCKRreceive /ORKRsend /ORKIsend /ORKRreceive /=. 
    rewrite !(if_true (_ && _ )) => //. 
    intro S.
    rewrite -syncIR_to_SyncIR /syncIR in S. smt.


     intro S.
    rewrite -syncIR_to_SyncIR /syncIR in S. smt.

    rewrite -(SyncIR (ind_pred i)).  by rewrite syncIR_to_SyncIR. 
    rewrite -syncIR_to_SyncIR. smt.


    rewrite Htau.
    simpl.

    ghave U : [SyncIR (ind_zero) => (i=ind_one) => (RKIsend@init = RKRreceive@R(i))].
    { intro S Eq. rewrite -syncIR_to_SyncIR /syncIR in S.
      case S. search RKRreceive@_.
      ++ rewrite /RKIsend /RKRreceive Eq.
         rewrite RKRsend_pred //. rewrite if_true //. 
         rewrite /gRecR.
         destruct S as [S1 ->].
         by rewrite exp_mult E_com exp_mult. 
      ++ smt.
    }
    rewrite U. auto. smt.
    have V : ind_succ (ind_pred i) = i. smt.
    rewrite V.  auto.


  -  rewrite /Opublic.  
    deduce. 
    rewrite /( |> ) in IH.    
    destruct IH as [fIH EIH].

    rewrite /( |> ).
    exists (fun (x :  _*_*_*_*_*_*(_*_*_*_*_*_*_*_*_)*_*_) => (
          (if SyncRI (i) then 
              
              (if HealthyR ( i) then 
                       (x#1) (i)  
              else  ((x#7)#2) ((x#3) (i)))
	       
         else 
            (if HealthyI (ind_pred i) then
               (x#9) i
             else  
             ((x#7)#2) ((x#4) i) )) , 
          if HealthyI i then (x#2) i else ((x#7)#2) ((x#5) i)
)).
    rewrite /=.
    rewrite /OCKRsend /OCKIsend /OCKIreceive /ORKRsend /ORKIsend /ORKIreceive /=. 
    rewrite !(if_true (_ && _ )) => //.
   
    intro S.
    rewrite -syncRI_to_SyncRI /syncRI in S. smt.


    intro S.
    rewrite -syncRI_to_SyncRI /syncRI in S. smt.

    rewrite -(SyncRI ( i)).  by rewrite syncRI_to_SyncRI. 
    by simpl.
 
    by simpl.

  - deduce with (deduce_stRCor (pred tau) tau' _); [1:auto]. 
    deduce with (deduce_stICor (pred tau) tau' _); [1:auto]. 

  - rewrite /input.
    deduce with IH.
    rewrite /( |> ).
    rewrite /( |> ) in IH.
    destruct IH as [get_frame IH].
    rewrite /Opublic.   
    exists (fun (x :  _*_*_*_*_*_*(_*_*_*_*_*_*_*_*_)*_*_) =>

       ((x#7)#1) (att (get_frame x (pred tau)))).
    simpl. by rewrite IH /= if_true //. 

  - rewrite /input.
    deduce with IH.
    rewrite /( |> ).
    rewrite /( |> ) in IH.
    destruct IH as [get_frame IH].
    rewrite /Opublic.   
    exists (fun (x :  _*_*_*_*_*_*(_*_*_*_*_*_*_*_*_)*_*_) =>

       ((x#7)#2) (att (get_frame x (pred tau)))).
    simpl. by rewrite IH /= if_true //. 
Qed.

global lemma DeduceFrame @set:S/left (tau, tau' : timestamp[const]) :
  [tau <= tau'] ->
  $(  (Oracles tau' tau' tau' tau') |> (frame@tau) ).
Proof.
  intro O.
  have I := DeduceFrameNoConst tau tau' O. 
  deduce with I.
Qed.

global lemma DeduceInputNoConst @set:S/left (tau, tau' : timestamp[const]) :
  [tau <= tau'] ->
  $(  (Oracles tau' tau' tau' tau') |> (fun t => if t <= tau then input@t) ).
Proof.
  intro Htau.
  rewrite /Oracles.
  ghave Ded : $(  (fun t => if t <= tau then frame@pred t)   |> (fun t =>  if t <= tau then input@t)).
  { 
   rewrite /( |> ).
   exists (fun fframe => (fun (t:timestamp)  => if t = init then empty else if t <= tau then att(fframe t))).
   simpl. 

   fa.
   case t=init.
   + intro Ord. rewrite if_true //. by rewrite if_true //.
   + case t<= tau.
     ++ intro Ord Neq. rewrite if_false //. rewrite if_true //. simpl.
        expand ~def input. rewrite if_false //. rewrite if_false //. rewrite if_true //. 
     ++ intro Ord Neq.    by rewrite if_false //. 
   }
  deduce with Ded.
  by deduce with (DeduceFrameNoConst tau tau' Htau).
Qed.

global lemma DeduceOutputNoConst @set:S/left (tau, tau' : timestamp[const]) :
  [tau <= tau'] ->
  $(  (Oracles tau' tau' tau' tau') |> (fun t => if t <= tau then output@t) ).
Proof.
  intro Htau.
  rewrite /Oracles.
  ghave Ded : $(  (fun t => if t <= tau then frame@t)   |> (fun t => if t <= tau then output@t)).
   {
   rewrite /( |> ).
   exists (fun fframe => (fun (t:timestamp)  => if t<= tau then if t = init then empty else snd(snd(fframe t)))). 
   simpl.
   search fun _ => _.  
   fa.
   case t=init.
   + intro Eq.
     simpl. by rewrite /output.
   + case (t<= tau). 
     ++ intro Ord Ninit. expand ~def frame. simpl.

        rewrite if_false //.
        rewrite if_false //.
        rewrite if_true // => /=.  
        rewrite if_true. 
        by apply is_exec. 
       by simpl. 
    ++ by simpl.   
   }
  deduce with Ded.
  by deduce with (DeduceFrameNoConst tau tau' Htau).
Qed.



