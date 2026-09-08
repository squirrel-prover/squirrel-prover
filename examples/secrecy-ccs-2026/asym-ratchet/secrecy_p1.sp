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
(* set smtSteps=200000. *)

(* ------------------------------ *)

(*****************************************************************)
(* Secrecy predicates:                                           *)
(* specific to this proof, used to make lemmas more concise      *)
(*****************************************************************)


(* Secret_target t1 t2 t3 tr side = oracles@t1 t2 t3 *> secret@side, tr *)
predicate Secret_target {set:system} {set: (tau1l, tau2l, tau3l, tau4l, taur:timestamp, t:int, n,n':index)} =
$( (Oracles tau1l tau2l tau3l tau4l)
     *>
     (if t=4 then 
        RKRsend@taur 
     else if t=3 then RKIsend@taur
     else if t=2 then RKRreceive@taur
     else if t=1 then RKIreceive@taur
     else if t=0 then ofG(g^(skR n ** skI n'))
)
   ).

include Int.
open Int.

(* Secret_prop t1 t2 t3 tr = if healthy@tr, then oracles@t1 t2 t3 *> secret@tr *)
predicate Secret_prop {set:system} {set: t:int, tau1l, tau2l, tau3l, tau4l, taur:timestamp} =
  [happens(tau1l, tau2l, tau3l, taur)] ->
Forall (n,n':index[const]),
    [(t=4 && HealthyR (getRi taur))
     || (t=3 && HealthyI (getIi taur)) 
     || (t=2 && HealthyR (ind_pred (getRi taur)) && not (SyncIR (ind_pred (getRi taur)))) 
     || ((t=1 && HealthyI (ind_pred (getIi taur)) && not (SyncRI (getIi taur)))
     || (t=0 && safeR n && safeI n')
    ) 
] ->
    (Secret_target tau1l tau2l tau3l tau4l taur t n n').

(* If secret@tr is secret from oracles@t1,t2,t3, then it is secret from
   any earlier oracles@t1',t2',t3' as well *)
global lemma Secret_earlier @set:S/left 
 (tau1l, tau1l', tau2l, tau2l', tau3l, tau3l', tau4l, tau4l', taur:timestamp[const], t:int[const]) :
  [tau1l' <= tau1l] ->
  [tau2l' <= tau2l] ->
  [tau3l' <= tau3l] ->
  [tau4l' <= tau4l] ->
    Secret_prop t tau1l  tau2l  tau3l tau4l  taur ->
    Secret_prop t tau1l' tau2l' tau3l' tau4l' taur.
Proof.
  intro Htau1 Htau2 Htau3 Htau4.
  rewrite /Secret_prop /Secret_target.  
  intro HS Hap n n' Heal.
  have _ := (HS _ n n' _); [1,2: auto].
 
  by deduce with (bigger_Oracles tau1l tau1l' tau2l tau2l' tau3l tau3l' tau4l tau4l').
Qed.

(**********************************************************************************************)
(* Structure of the proof: 
   - We want to prove in the end: forall tau0 taur, oracles@tau0 *> secret@taur


   - We split the proof based on which of the oracles is at the latest
     timestamp. This enables us to efficiently get rid of the hash, as
     being at the latest timestamp often implies that the hash is fresh.
     We split this in four lemmas, rewinding each argument of Secret_prop
     in the good order.
     
     The structure of the proof can be obsevered by executing the lemma
     `Secret_induction` in `secrecy_p3.sp`.
*)
(**********************************************************************************************)


 (******************************)
 (* Case 0: everything is init *)
 (******************************)
global lemma Secret_init @set:S/left :
   Forall (t:int [const]), Secret_prop t init init init init init.
Proof.
  rewrite /Secret_prop /Secret_target /=.
  intro side Hhap n n2 Hside.
  rewrite /Oracles /OCKRsend /OCKIsend /OCKRreceive /OCKIreceive /ORKRsend /ORKIreceive /ORKIsend /ORKRreceive /=.
  deduce.
  ghave [I | I | I | I | I] : [side=4 || side=3 || side=2 || side=1 || side=0] by auto. 
  + rewrite if_true; [1:auto].
    rewrite /RKRsend. 
    rewrite /Opublic.    
    prf ~left 8.   
        rewrite /RKIsend. 
        prf ~right 0. 
        apply (ded_right fst). simpl. by fresh.
    by fresh.       

  + rewrite if_false; [1: smt ~no_macros].
    rewrite if_true; [1:auto].
    rewrite /RKIsend. 
    rewrite /Opublic.
    prf ~left 8.   
        rewrite /RKIsend. 
        prf ~right 0. 
        apply (ded_right fst). simpl. by fresh.

    prf ~right 0. 
    apply (ded_right fst). simpl. 
    by fresh.

  + rewrite if_false; [1: smt ~no_macros].
    rewrite if_false; [1: smt ~no_macros].
    rewrite if_true; [1:auto].
    rewrite /RKRreceive.
    by fresh.

  + rewrite if_false; [1: smt ~no_macros].
    rewrite if_false; [1: smt ~no_macros].
    rewrite if_false; [1: smt ~no_macros].    
    rewrite /RKIreceive.
    rewrite if_true; [1:auto].
    rewrite /Opublic.
    prf ~left 8.   
        rewrite /RKIsend. 
        prf ~right 0. 
        apply (ded_right fst). simpl. by fresh.   
    by fresh.

  +  rewrite if_false; [1: smt ~no_macros].
    rewrite if_false; [1: smt ~no_macros].
    rewrite if_false; [1: smt ~no_macros].    
    rewrite if_false; [1: smt ~no_macros].
    rewrite if_true; [1:auto].
    ghave [R1 | R2] : [ (safeR n && safeI (n2)) || not  (safeR n && safeI (n2))]; 1: rewrite or_comm -impl_charac; intro _; assumption.
    ++  
    rewrite /Opublic.     
        prf ~left 8.   
        rewrite /RKIsend. 
        prf ~right 0. 
        apply (ded_right fst). simpl. by fresh.   
    rewrite /( *> ).
    intro f.
    intro F.
    apply f_apply toG in F.
    rewrite toG_ofG in F.
    gdh F, g. 
      +++ by simpl. 
      +++ by simpl. 
    ++ by have _ : false by smt. 
Qed.




 (****************************************)
 (* Case 1: OCKRsend/OCKIsend is maximum *)
 (****************************************)

 (* Illustration legend:
    * may be leaked
    ! message handled in this case
    ? may be the secret *)

 (* Simplification : The trace alternate R and I and maximal tau is R

               Rlice                     Iob
  -----------------------------------------------------------
                r1*          c1* <--h'-- r1?*
                 |                        |
                 |h                       |h
                 V                        V
                 r2?* --h'--> c2*         r2*
                 |                        |
 ............... |h ......                |h
                 V        .               V
                 r3*       .  c3* <--h'-- r3?*
                 |          .             |
                 |h          ............ |h ...............
                 V                        V
                 r4?* --h'--> c4!         r4
  *)
  

 (* We will have to eliminate the extra h' hash produced
    by OCKRsend or OCKIsend on the left hand side. *)

 (* Depending on whether tau0 is R i, I i, or something else,
    either a h'(RKRsend), h'(RKIsend), or nothing, is added on the left hand side. *)
 (* The difficult cases are the first two: we will have to eliminate the extra h'
    hash produced by OCKRsend or OCKIsend. *)


global lemma Secret_case1 @set:S/left (tau0:timestamp[const]):
  [init < tau0]
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur <= tau0] ->
      (Secret_prop t (pred tau0) tau0 tau0 tau0 taur))
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur <= tau0] ->
      (Secret_prop t tau0 tau0 tau0 tau0 taur)).
Proof.
  intro HI HP taur side Htaur.
  rewrite /Secret_prop /Secret_target /=.
  intro Hhap n n2 Heal.

  ghave [[i Htau] | [i Htau] | Zt] :
      (Exists (i:index [const]), [tau0=R i]) 
   \/ (Exists (i:index [const]), [tau0=I i]) 
   \/ (Forall (i:index [const]), [tau0<>R i && tau0<>I i ]).

   * (* proving the disjunction (easy but no smt because global unfortunately) *)
     case tau0;
     try ( (intro [j R] + intro j); right; right; intro j'; constraints ).  
     intro [i R]. left. by exists i.
     intro [i I]. right. left. by exists i.


   (**********************************)
   (* Case 1.1: tau0=R i             *)
   (**********************************)
   (* We isolate from OCKRsend the added thing, OCKIsend does not change
      (compared to pred tau0) *)
   * rewrite Htau in *.
     rewrite /Oracles.
     deduce with (OCKRsend_split i). by constraints. 
     rewrite stable_OCKIsend. intro i0 T; by constraints. 
      
     (* Depending on HealthyR i, either a h' is added in OCKRsend or not. *)   
     ghave [H|H] : [ (HealthyR i) || not(HealthyR i) ]; 1: rewrite or_comm -impl_charac; intro _; assumption.

     (* case HealthyR i: this is the case where we must eliminate h'(RKRsend).
         Iasically, we apply PRF to remove it, and then IH.
         The side-conditions of PRF:
          - (phi_prf) is proved thanks to no-collision lemmas,
             except the case of the RO, which holds by IH.
          - secrecy of RKRsend is proved using IH. *)
     ** rewrite H /=.

        (* We unroll a bit more the rhs before prf, as otherwise, it
           finds an occurence here, the R j <= taur instead of R j < taur. 
           Three lemmas stR, stI, RKRreceive, we keep them around
           to rewrite them back once prf has been applied. *)

               
        rewrite /Opublic.  
         rewrite expand_ORKRreceive. 
        rewrite expand_OCKRreceive.

        rewrite expand_rhs; [1: constraints].

        (* prf to remove the additional h'(RKRsend) *)
        prf ~left ~under_hash 17.
        + { (* all goals for the first prf side-condition (phi_prf) *)
           repeat split.
           ++ intro j Eq. by apply NoColRKRsendRKIsend; [1:constraints].
           ++ by apply NoColRKRsendRKIsend; [1:constraints].
           ++ intro i' Ord.                
              have C := NoColRKRsendRKRreceive (R i) (R i') _; [1:constraints]. 
              by rewrite /RKRreceive in C.
           ++ intro i' Ord. 
              by have _ := NoColIThenR i i' _; [1:constraints].  
           ++ intro j I. by apply NoColRKRsend; [1:constraints].
           ++ intro I. 
              have I0 : happens(R i, Izero).
               {
                 repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                 try constraints.
               }
             have C := NoColRKRsendRKIsend _ _ I0. 
             by rewrite /RKIsend in C.
           ++ intro j I.
              have I0 : happens(R i, R j).
               {
                 repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                 try constraints.
               }
              by have C := NoColRKRsendRKRreceive _ _ I0. 
           ++ intro j I.
              have I0 : happens(R j, R i). 
               {
                 repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                 try constraints.
               }
              apply NoColRKRsend. by simpl. 
              intro Eq. subst j, i. 
              repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
              try constraints. 
              +++ smt ~no_macros.
           ++ intro j I.
              have I0 : I j < R i. 
               { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                 constraints.
               }
              by apply NoColIThenR i j _; [1:constraints].
           ++ intro j I. 
              have I0 : happens(R i, I j).
               { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                 try constraints.
               }
              by apply NoColRKRsendRKIsend; [1:constraints].
           (* For the RO, we use the HP hypothesis to show secret@R i cannot have been
              sent to the oracle *)
           ++ intro j I.
              have I0 : RO' j < R i. 
               { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                 constraints.
               }
              clear I.
              rewrite /input.
              intro Ded.
              
              (* HP says: oracles@pred t0, t0, t0 *> secret@R i *)
              have ZIH := (HP (R i) 4 _); [1:auto].
              
              (* then SecretEarlier to get RO' j instead of t0/pred t0 *)
              have DedNIH :=
                Secret_earlier (pred (R i)) (RO' j) 
                               (R i) (RO' j)
                               (R i) (RO' j)
                               (R i) (RO' j)
                               (R i) 4
                               _ _ _ _ ZIH;
                [1,2,3,4:constraints].

              rewrite /Secret_prop /Secret_target in DedNIH.
              have NDed  := DedNIH _  n n2 _  => {DedNIH}.
              auto. auto.

              apply if_true_ded in NDed; [1: auto]. 

              have DedF := DeduceFrame (pred (RO' j)) (RO' j) _; 1:constraints. 
              
              apply (no_ded_ded _ _ _ NDed) in DedF => {NDed}.
              rewrite /( *>) in DedF.
              by have _ := DedF att.
          }
       
        (* second prf side-condition:
           the hashed value (ie RKRsend) is secret *)
        + deduce.
         (* we use the induction hypothesis HP: oracles@pred t0, t0, t0 *> secret@R i *)
          have ZIH := HP (R i) 4 _; [1:auto].
          rewrite /Secret_prop /Secret_target in ZIH;
          have DedNIH := ZIH _ n n2 _; [1,2:by simpl]; clear ZIH.
          
          apply if_true_ded in DedNIH. auto. 
          rewrite /Oracles /Opublic in DedNIH.  
          rewrite -expand_ORKRreceive -expand_OCKRreceive.    
          apply DedNIH.
         
        (* done with applying prf: h'(RKRsend) is gone on the left *)
        + 
          rewrite -expand_rhs; [1:constraints]. 
          rewrite -expand_ORKRreceive -expand_OCKRreceive.
        (* then we conclude with HP *)
          have ZIH := HP taur side _; [1:auto].
          rewrite /Secret_prop /Secret_target in ZIH;
          have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.

          rewrite /Oracles /Opublic in DedNIH.           
          apply DedNIH.
    
     (* case not HealthyR i: we just apply HP directly *)
     ** rewrite (if_false ( (HealthyR i) )). auto. deduce.
        have ZIH := HP taur side _; [1:auto].
        rewrite /Secret_prop /Secret_target in ZIH;
        have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.

        rewrite /Oracles /Opublic in DedNIH.           
        apply DedNIH.
     

  (**********************************)
  (* Case 1.2: tau0=I i is maximum *)
  (**********************************)
   * rewrite Htau.
     rewrite /Oracles.
     deduce with (OCKIsend_split i). by constraints. 
     rewrite stable_OCKRsend.  intro i0 T. by constraints. 

     ghave [H|H] : [ (HealthyI i) || not(HealthyI i)]; 1: rewrite or_comm -impl_charac; intro _; assumption.

     (* case HealthyI i *)
     ** rewrite H /=.
        (* We unroll a bit more the rhs before prf, as otherwise, it
           finds an occurence here, the R j <= taur instead of R j <
           taur. *)

        rewrite expand_rhs; [1:constraints].
       
        rewrite expand_ORKIreceive.       

        rewrite expand_OCKIreceive.
        
        rewrite /Opublic.  
    
        (* prf to remove the additional h'(RKIsend) on the left *)
        prf ~left ~under_hash 17.
        + { (* all goals for the first prf side-condition (phi_prf) *)
            repeat split.
            ++ intro j Eq.
               rewrite neq_sym.
               by apply NoColRKRsendRKIsend; [1:constraints].
            ++ have NoCol := NoColI (i, true) (ind_zero, true). 
               smt.
            ++ intro j [Ord _].
               by have _ :=  NoColRThenI i j _; [1:constraints].
            ++ intro j Ord.
               have I0 : happens(I i, I j). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
               by have _ :=  NoColRKIsendRKIreceive (I i) (I j) I0.
            ++ intro j I.
               by apply NoColRKIsend; [1:constraints].
            ++ intro I.
	       have I0 : happens(I i). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
               by apply NoColRKIsendIzero; [1:constraints].
            ++ intro j I.
               have I0 : R j < I i.
                { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                  constraints.
                }
               by apply NoColRThenI i j _; [1:constraints].
            ++ intro j I.  
               have I0 : happens(R j, I i). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
               rewrite neq_sym.
               by apply NoColRKRsendRKIsend; [1:constraints].
            ++ intro j I.
               have I0 : happens(I i, I j). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
               by apply NoColRKIsendRKIreceive; [1:constraints].
            ++ intro j I.
               have I0 : happens(I j, I i). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
               apply NoColRKIsend. by simpl. 
               intro Eq.
               subst j, i.
               rewrite Htau in *.
               repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
               try constraints. 
               +++ smt ~no_macros.



            (* For the RO, we use the HP hypothesis to show secret@R i
               cannot have been
               sent to the oracle *)
            ++ intro j I.
               have I0 : RO' j < I i.
                { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                  constraints.
                }
               clear I.
               rewrite /input.
               intro Ded.

              (* HP says: oracles@pred t0, t0, t0 *> secret@I i *)
              have ZIH := (HP (I i) 3 _); [1:auto].
              
              (* then SecretEarlier to get RO' j instead of t0/pred t0 *)
              rewrite Htau in ZIH.
              have DedNIH0 :=
                Secret_earlier (pred (I i)) (RO' j) 
                               (I i) (RO' j)
                               (I i) (RO' j)
                               (I i) (RO' j)
                               (I i) 3
                               _ _ _ _ ZIH;
                [1,2,3,4:constraints].
              rewrite /Secret_prop /Secret_target in DedNIH0.
              have DedNIH := DedNIH0 _ n  n2 _; [1,2: by simpl]; clear DedNIH0. 

              have DedF := DeduceFrame (pred (RO' j)) (RO' j) _; 1:constraints. 
              
               apply if_false_ded in DedNIH. by simpl.
 
               apply (no_ded_ded _ _ _ DedNIH) in DedF => {DedNIH}.
      
               rewrite /( *>) in DedF.
                   
               by have _ := DedF att.
          }
       
        (* second prf side-condition: the hashed message (ie RKIsend) is secret *)
        + deduce.
         (* we use the induction hypothesis HP: oracles@pred t0, t0, t0 *> secret@I i *)
          have ZIH := HP (I i) 3 _; [1:auto].
          rewrite /Secret_prop /Secret_target in ZIH;
          have DedNIH := ZIH _ n n2 _; [1,2:by simpl]; clear ZIH.

          apply if_false_ded in DedNIH. by simpl. 
          apply if_true_ded in DedNIH. by simpl. 

          rewrite Htau /Oracles /Opublic in DedNIH.  
          rewrite -expand_ORKIreceive -expand_OCKIreceive. 
          apply DedNIH.
         
        (* done with applying prf: h'(RKIsend) is gone on the left *)
        + rewrite -expand_rhs; [1:constraints]. 
          rewrite -expand_ORKIreceive -expand_OCKIreceive. 
        (* then we conclude with HP *)
          have ZIH := HP taur side _; [1:auto].
          rewrite Htau /Secret_prop /Secret_target in ZIH;
          have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.

          rewrite /Oracles /Opublic in DedNIH.           
          apply DedNIH.
    
     (* case not HealthyI i *)
     ** rewrite (if_false ( (HealthyI i) )); [1: auto].
        deduce.
        have ZIH := HP taur side _; [1:auto].
        rewrite Htau /Secret_prop /Secret_target in ZIH;
        have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.

        rewrite /Oracles /Opublic in DedNIH.           
        apply DedNIH.


  (*************************************)
  (* Case 1.3: tau0<>R/I i is maximum *)
  (*************************************)
  * simpl.
    rewrite /Oracles.
    rewrite stable_OCKRsend.
     { intro i T. by have _ := Zt i. }  (* scale Oh' one step back *)
    rewrite stable_OCKIsend.
     { intro i T. by have _ := Zt i. } (* scale Oh' one step back *)

    have ZIH := HP taur side _; [1:auto].
    rewrite /Secret_prop /Secret_target in ZIH.
    have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.
   
    rewrite /Oracles in DedNIH.
    apply DedNIH.
Qed.





 (**********************************************)
 (* Case 5: OCKRreceive/OCKIreceive is maximum *)
 (**********************************************)

 (* We will have to eliminate the extra h' hash produced
    by OCKRsend or OCKIsend on the left hand side. *)

 (* Depending on whether tau0 is R i, I i, or something else,
    either a h'(RKRreceive), h'(RKIreceive), or nothing, is added on the left hand side. *)


global lemma Secret_case5 @set:S/left (tau0:timestamp[const]):
  [init < tau0]
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur <= tau0] ->
      (Secret_prop t (pred tau0) tau0 tau0 (pred tau0) taur))
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur <= tau0] ->
      (Secret_prop t (pred tau0) tau0 tau0 (tau0) taur)).
Proof.
  intro HI HP taur side Htaur.
  rewrite /Secret_prop /Secret_target /=.
  intro Hhap n n2 Heal.

  ghave [[i Htau] | [i Htau] | Zt] :
      (Exists (i:index [const]), [tau0=R i]) 
   \/ (Exists (i:index [const]), [tau0=I i]) 
   \/ (Forall (i:index [const]), [tau0<>R i && tau0<>I i ]).

   * (* proving the disjunction  *)
     case tau0;
     try ( (intro [j R] + intro j); right; right; intro j'; constraints ).  
     intro [i R]. left. by exists i.
     intro [i I]. right. left. by exists i.


   (**********************************)
   (* Case 5.1: tau0=R i             *)
   (**********************************)
   (* We isolate from OCKRreceive the added thing, OCKIreceive does not change
      (compared to pred tau0) *)
   * rewrite Htau in *.
     rewrite /Oracles.
     deduce with (OCKRreceive_split i). by constraints. 
     rewrite stable_OCKIreceive. intro i0 T; by constraints. 
      
     (* Depending on HealthyR (i-1) and sync, either a h' is added in OCKRreceive or not. *)   
     ghave [H|H] : [ (HealthyR (ind_pred i) && not (SyncIR (ind_pred i))) || not((HealthyR (ind_pred i) && not (SyncIR (ind_pred i)))) ]; 1: rewrite or_comm -impl_charac; intro _; assumption.

     (* case HealthyR i: this is the case where we must eliminate h'(RKRreceive).
         Iasically, we apply PRF to remove it, and then IH.
         The side-conditions of PRF:
          - (phi_prf) is proved thanks to no-collision lemmas,
             except the case of the RO, which holds by IH.
          - secrecy of RKRsend is proved using IH. *)
     ** rewrite H /=.
               
        rewrite /Opublic.  

        rewrite expand_ORKRsend. 

        rewrite expand_rhs; [1: constraints].

        (* prf to remove the additional h'(RKRreceive) *)
        prf ~left ~under_hash 17.
        + { (* all goals for the first prf side-condition (phi_prf) *)
           repeat split.
           ++ intro i' Ord. by have _ := NoColRKRsendRKRreceive (R i') (R i); [1:constraints].
           ++ intro i0 I. 
	      by apply NoColRKRreceiveRKIsend; [1:constraints].
           ++ by apply NoColRKRreceiveRKIsend; [1:constraints].
           ++ intro i0. by have   := NoColRKRreceiveRKIreceive (R i) (I i0); [1:constraints].
           ++ intro j I. by apply NoColRKRreceive; [1:constraints].
           ++ intro I.	      
	      have I0 : happens(Izero).
               { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                 try constraints. 
		 }.
              clear I.
              by apply NoColRKRreceiveRKIsend; [1:constraints].
           ++ intro j I.   have I0 : R j < R i. 
               { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                 try constraints.
                 +++ smt ~no_macros.
               }
               clear I.
		by apply NoColRKRreceive; [1:constraints].
           ++ intro i' Ord. 
	      have I0 : happens(R i', R i).
               { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                 try constraints.
                 +++ smt ~no_macros.
		}
                clear Ord.
		by have _ := NoColRKRsendRKRreceive (R i') (R i) I0; [1:constraints].
           ++ intro j I. 
              have I0 : happens(R i, I j).
               { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                 try constraints.
               }
              by apply NoColRKRreceiveRKIreceive; [1:constraints].
           ++ intro j I. 
              have I0 : happens(R i, I j).
               { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                 try constraints.
               }
              by apply NoColRKRreceiveRKIsend; [1:constraints].

           (* For the RO, we use the HP hypothesis to show secret@R i cannot have been
              sent to the oracle *)
           ++ intro j I.
              have I0 : RO' j < R i. 
               { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                 constraints.
               }
              clear I.
              rewrite /input.
              intro Ded.

              
              (* HP says: oracles@pred t0, t0, t0 *> secret@R i *)
              have ZIH := (HP (R i) 2 _); [1:auto].
              
              (* then SecretEarlier to get RO' j instead of t0/pred t0 *)
              have DedNIH :=
                Secret_earlier (pred (R i)) (RO' j) 
                               (R i) (RO' j)
                               (R i) (RO' j)
                               (pred (R i)) (RO' j)
                               (R i) 2
                               _ _ _ _ ZIH;
                [1,2,3,4:constraints].

              rewrite /Secret_prop /Secret_target in DedNIH.
              have NDed  := DedNIH _ n n2 _ => {DedNIH}.
              auto. auto.

              apply if_false_ded in NDed; [1: auto]. 
              apply if_false_ded in NDed; [1: auto]. 
              apply if_true_ded in NDed; [1: auto]. 

              have DedF := DeduceFrame (pred (RO' j)) (RO' j) _; 1:constraints. 
              
              apply (no_ded_ded _ _ _ NDed) in DedF => {NDed}.
              rewrite /( *>) in DedF.
              by have _ := DedF att.
          }
       
        (* second prf side-condition
           the hashed value (ie RKRreceive) is secret *)
        + deduce.
         (* we use the induction hypothesis HP: oracles@pred t0, t0, t0 *> secret@R i *)
          have ZIH := HP (R i) 2 _; [1:auto].
          rewrite /Secret_prop /Secret_target in ZIH;
          have DedNIH := ZIH _ n n2 _; [1,2:by simpl]; clear ZIH.
          
          apply if_false_ded in DedNIH. auto. 
          apply if_false_ded in DedNIH. auto. 
          apply if_true_ded in DedNIH. auto. 

          rewrite /Oracles /Opublic in DedNIH.  
          rewrite -expand_ORKRsend.
          apply DedNIH.
         
        (* done with applying prf: h'(RKRsend) is gone on the left *)
        + 
          rewrite -expand_rhs; [1:constraints]. 
          rewrite -expand_ORKRsend.
        (* then we conclude with HP *)
          have ZIH := HP taur side _; [1:auto].
          rewrite /Secret_prop /Secret_target in ZIH;
          have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.

          rewrite /Oracles /Opublic in DedNIH.           
          apply DedNIH.
    
     (* case not HealthyR i or sync: we just apply HP directly *)
     ** rewrite if_false.  auto. deduce.
        have ZIH := HP taur side _; [1:auto].
        rewrite /Secret_prop /Secret_target in ZIH;
        have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.

        rewrite /Oracles /Opublic in DedNIH.           
        apply DedNIH.


  (**********************************)
  (* Case 5.2: tau0=I i is maximum *)
  (**********************************)
   * rewrite Htau.
     rewrite /Oracles.
     deduce with (OCKIreceive_split i). by constraints. 
     rewrite stable_OCKRreceive.  intro i0 T. by constraints. 

     ghave [H|H] : [ (HealthyI (ind_pred i) && not (SyncRI i)) || not((HealthyI (ind_pred i) && not (SyncRI i)))] ; 1: rewrite or_comm -impl_charac; intro _; assumption.

     (* case HealthyI i-1 and unsync *)
     ** rewrite H /=.
        (* We unroll a bit more the rhs before prf, as otherwise, it
           finds an occurence here, the R j <= taur instead of R j <
           taur. *)

        rewrite expand_rhs; [1:constraints].


        rewrite expand_ORKIsend expand_ORKIreceive. 

        rewrite /Opublic.  
    
        (* prf to remove the additional h'(RKIreceive) on the left *)
        prf ~left ~under_hash 17.
        + { (* all goals for the first prf side-condition (phi_prf) *)
            repeat split.
            ++ intro j I. 
	       rewrite neq_sym.
   	       by apply NoColRKIreceiveRKRsend; [1:constraints].
            ++ intro j Ord.
               have I0 : happens(I j, I i). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
               by have _ :=  NoColRKIsendRKIreceive (I j) (I i) I0.
            ++ have NoCol := NoColI (i, false) (ind_zero, true).  
               smt.
            ++ intro j Eq.
               rewrite neq_sym.
               by apply NoColRKRreceiveRKIreceive; [1:constraints].
            ++ intro j Eq.
               by apply NoColRKIreceive; [1:constraints].
            ++ have NoCol := NoColI (i, false) (ind_zero, true).  
               smt.
            ++ intro j I.
               have I0 : happens(R j, I i). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
               rewrite neq_sym.
               by apply NoColRKRreceiveRKIreceive; [1:constraints].
            ++ intro j I.
               have I0 : happens(R j, I i). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
	       rewrite neq_sym.
   	       by apply NoColRKIreceiveRKRsend; [1:constraints].
            ++ intro j I.
               have I0 : I j < I i. 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
                clear I.
               by apply NoColRKIreceive _ _; [1:constraints].
            ++ intro j I.
               have I0 : happens(I j, I i). 
                { repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                  try constraints.
                }
               rewrite neq_sym.
               by apply NoColRKIsendRKIreceive _ _ I0. 

            (* For the RO, we use the HP hypothesis to show secret@R i
               cannot have been
               sent to the oracle *)
            ++ intro j I.
               have I0 : RO' j < I i.
                { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                  constraints.
                }
               clear I.
               rewrite /input.
               intro Ded.


              (* HP says: oracles@pred t0, t0, t0 *> secret@I i *)
              have ZIH := (HP (I i) 1 _); [1:auto].
              
              (* then SecretEarlier to get RO' j instead of t0/pred t0 *)
              rewrite Htau in ZIH.
              have DedNIH0 :=
                Secret_earlier (pred (I i)) (RO' j) 
                               (I i) (RO' j)
                               (I i) (RO' j)
                               (pred (I i)) (RO' j)
                               (I i) 1
                               _ _ _ _ ZIH;
                [1,2,3,4:constraints].
              rewrite /Secret_prop /Secret_target in DedNIH0.
              have DedNIH := DedNIH0 _ n n2 _; [1,2: by simpl]; clear DedNIH0. 

              have DedF := DeduceFrame (pred (RO' j)) (RO' j) _; 1:constraints. 
              
               apply if_false_ded in DedNIH. by simpl.
 
               apply (no_ded_ded _ _ _ DedNIH) in DedF => {DedNIH}.
      
               rewrite /( *>) in DedF.
                   
               by have _ := DedF att.
          }
       
        (* second prf side-condition: the hashed message (ie RKIreceive) is secret *)
        + deduce.
         (* we use the induction hypothesis HP: oracles@pred t0, t0, t0 *> secret@I i *)

         rewrite -expand_ORKIsend -expand_ORKIreceive. 

          have ZIH := HP (I i) 1 _; [1:auto].
          rewrite /Secret_prop /Secret_target in ZIH;
          have DedNIH := ZIH _ n n2 _; [1,2:by simpl]; clear ZIH.

          apply if_false_ded in DedNIH. by simpl. 
          apply if_false_ded in DedNIH. by simpl. 
          apply if_false_ded in DedNIH. by simpl. 
          apply if_true_ded in DedNIH. by simpl. 

          rewrite Htau /Oracles /Opublic in DedNIH.  
          apply DedNIH.
         
        (* done with applying prf: h'(RKIsend) is gone on the left *)
        + rewrite -expand_rhs; [1:constraints]. 
         rewrite -expand_ORKIsend -expand_ORKIreceive. 

        (* then we conclude with HP *)
          have ZIH := HP taur side _; [1:auto].
          rewrite Htau /Secret_prop /Secret_target in ZIH;
          have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.

          rewrite /Oracles /Opublic in DedNIH.           
          apply DedNIH.
    
     (* case not HealthyI i *)
     ** rewrite (if_false); [1: auto].
        deduce.
        have ZIH := HP taur side _; [1:auto].
        rewrite Htau /Secret_prop /Secret_target in ZIH;
        have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.

        rewrite /Oracles /Opublic in DedNIH.           
        apply DedNIH.


  (*************************************)
  (* Case 5.3: tau0<>R/I i is maximum *)
  (*************************************)
  * simpl.
    rewrite /Oracles.
    rewrite stable_OCKRreceive.
     { intro i T. by have _ := Zt i. }  (* scale Oh' one step back *)
    rewrite stable_OCKIreceive.
     { intro i T. by have _ := Zt i. } (* scale Oh' one step back *)

    have ZIH := HP taur side _; [1:auto].
    rewrite /Secret_prop /Secret_target in ZIH.
    have DedNIH := ZIH _ n n2 _; [1,2:constraints]; clear ZIH.
   
    rewrite /Oracles in DedNIH.
    apply DedNIH.
Qed.

(**********************************************)
(* Case 3.1: taur is maximum, and side=3 or 4 *)
(**********************************************)	

(* Simplification : The trace alternate R and I and maximal tau is R

              Rlice                     Iob
-----------------------------------------------------------
                r1*          c1* <--h'-- r1?*
                |                        |
                |h                       |h
                V                        V
                r2?* --h'--> c2*         r2*
                |                        |   
............... |h ......                |h  tau1l < taur
                V        .               V
                r3*       .  c3* <--h'-- r3?*
                |          .             |
                |h          ............ |h ...............
                V                        V
                r4?*! --h'--> c4         r4
*)

(* We will have to eliminate the extra hash h produced by RKRsend or
RKIsend on the right hand side. *)



global lemma Secret_case3_1 @set:S/left (tau0:timestamp[const]):
[init < tau0]
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur < tau0 || (taur = tau0 && t < 3)] ->
      (Secret_prop t (pred tau0) (tau0) tau0 (pred tau0) taur))
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur <= tau0] ->
      (Secret_prop t (pred tau0) (tau0) tau0 (pred tau0) taur)).
Proof.
 (* We prove the secrecy of stR/ISend, potentially using RKRreceive/RKIreceive. *)
  intro Hap IH taur.  
  intro side Hap0. 
  ghave [H | H] : [taur < tau0 || taur = tau0]; 1: by simpl. {
    apply IH.
    by left. 
  }

  ghave [Hs | Hs] : [(side<3) || 3 <= side]; 1: by smt.  {
    apply IH.
    by right. 
  }


  rewrite H in *.
  clear H Hap0 taur.
  ghave [[i Htau] | [i Htau] | Zt] :
                             (Exists (i:index [const]), [tau0=R i]) 
                          \/ (Exists (i:index [const]), [tau0=I i]) 
                          \/ (Forall (i:index [const]), [tau0<>R i && tau0<>I i ]).
  * case tau0; try ((intro [j R] + intro j); right; right; intro j'; constraints).  
    + intro [i R]. left. by exists i.
    + intro [i I]. right. left. by exists i.

  (**********************************)
  (* Case 3.1.1: taur=R i is maximum *)
  (**********************************)

  * rewrite /Secret_prop /Secret_target.
    intro Hap1 n n2 Heal.
    rewrite Htau in *.
    clear Htau Hap1.
    (* we quickly take care of the value of the case if `side` is for I. *)
    ghave [I | I] : [side=3 || not(side=3)]; 1: rewrite or_comm -impl_charac; intro _; assumption.
   {
      rewrite if_false; 1: by smt ~no_macros.
      rewrite (if_true); 1: by smt ~no_macros.
      rewrite /getIi   in Heal.
      rewrite /RKIsend.
      rewrite /Secret_prop /Secret_target in IH.
      have IH0 := IH (pred (R i)) side _ _ n n2 _. smt ~no_macros. constraints. by left. 
      rewrite if_false in IH0; 1: by smt ~no_macros.
      by rewrite (if_true) in IH0; 1: by smt ~no_macros.
    }

    ghave I1 : [side=4]; 1: by smt ~no_macros. 
    
    rewrite I1 /= in * => {I1 I}.

    rewrite /getRi in Heal.  
    rewrite /RKRsend.
    rewrite /Oracles /Opublic.

    rewrite expand_ORKRreceive.

    (* Here, no need to rewrite anything, we apply prf right directly. *)
    prf ~right ~under_hash 0. {
      (* Most cases are solved with a non-collision lemma. *)
      repeat split.
      - (* `RKRreceive@R i <> RKRsend@R i0` *)
        have H : RKRreceive@R i <> RKRsend@pred(R i); 2: auto.
        rewrite neq_sym.
        apply NoColRKRsendRKRreceive.
        constraints.

      - (* `RKRreceive@R i <> RKRsend@R j` *)
        simpl.


        intro i0 I H F.
        have I0 : R i0 <= R i. { 
          repeat (destruct I as [[i1 R]|I] + destruct I as [_|I]); try constraints.
        }
        apply (f_apply fst) in F.
        rewrite /= in F.
        by have NoCol := NoColRKRsendRKRreceive (pred (R i0)) (R i) _; [1:constraints]. 

      - (* `RKRreceive@R i <> RKRsend@init` *)
        simpl.
        intro F.
        apply (f_apply fst) in F.
        rewrite /= in F.
        by have NoCol := NoColRKRsendRKRreceive init (R i) _; [1:constraints].
      - (* Here, we prove the the attacker cannot deduce `gSendR i@R i` before
           the action `R i` due to the freshness of `a i`. *)
        intro j I. 
        have I0 : RO j < R i. { 
          repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); constraints.
        }
        clear I Hap.
        intro Ded.
        (* `Ded` implies that `frame@pred RO j |> gSendR i@R i`.
            However `gSendR i@R i = x ^ a i` with `x` known by the attacker
            at `pred (R i)` and `a i` fresh before `R i`.
            So, we rewrite `Ded` to have `Ded : a i = y` with `a i` fresh in `y` *)
        apply f_apply (fun x => dlog (toG (snd x))) in Ded.
        rewrite /= /gSendR /gI /= E_com in Ded.
        apply mult_inv_l in Ded.
        fresh Ded => //; smt ~no_macros.


      - (* `RKRreceive@R i <> RKRsend@R j` *)
        simpl.

        intro i0 I F.
        have I0 : R i0 <= R i. { 
          repeat (destruct I as [[i1 R]|I] + destruct I as [_|I]); try constraints.
        }
        apply (f_apply fst) in F.
        rewrite /= in F.
        by have NoCol := NoColRKRsendRKRreceive (pred (R i0)) (R i) _; [1:constraints].    

      - (* `RKRreceive@R i <> RKRreceive@R j` if `R j <> R i` *)
        simpl.
        intro j I. 
        have I0 : R j < R i. {
          repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]); try constraints.
          + smt ~no_macros. 
        }
         by have _ := NoColRKRreceive i j _ _; [1:constraints].
      - (* `RKRreceive@R i <> RKIsend@I j` if `I j` happens before `R i`. *)
        simpl.
        intro j I.    
        have I0 : I j < R i. {
          repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); constraints.
        }
        simpl.
        by have H := NoColIThenR i j _; [1:constraints].
      - (* `RKRreceive@R i <> SK` *)
        simpl.
        intro I F.
        apply (f_apply fst) in F.
        rewrite /= in F.
        by have NoCol := NoColRKRsendRKRreceive init (R i) _; [1:constraints].
      - (* `RKRreceive@R i <> RKIreceive@I i0` *)
        simpl.
        intro i0 I F.
        have I0 : I i0 < R i. {
          repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); constraints.
        }
        clear I Hap IH.
        by have NoCol := NoColRKRreceiveRKIreceive (R i) (I i0) _; 1: constraints.
    }
    simpl.


    (* either the first or the second element of the pair will be secret,
       depending on the following. *)
    ghave [H1|H1] : [ ( (HealthyR (ind_pred i) && not(SyncIR (ind_pred i))) || (SyncIR (ind_pred i) && HealthyI (ind_pred i))) 
                     || not(((HealthyR (ind_pred i) && not(SyncIR (ind_pred i))) || (SyncIR (ind_pred i) && HealthyI (ind_pred i)) ))] ; 1: rewrite or_comm -impl_charac; intro _; assumption.
    - case H1.
      -- (* use HealthyR i-1 to apply IH. *)
      rewrite -expand_ORKRreceive.  

      rewrite /Secret_prop /Secret_target in IH.
      apply (ded_right fst). simpl.


      have IH0 := IH (R i) 2 _ _ n n2.  constraints.  smt ~no_macros.

      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_true in IH0; 1: by smt ~no_macros.
      rewrite /Oracles /Opublic in IH0.  by apply IH0. 

      (* use `SyncIR (i-1)` to rewrite `RKRreceive` into `RKIsend`,
         which is secret by induction and `HealthyI (i-1)` *)
   --         rewrite -syncIR_to_SyncIR in H1.

      (*First, we prove `I(i-1) <R(i)` with `SyncIR(i-1)`.*)
      have I : (i <> ind_one => I(ind_pred i) < R i). {
         localize H1 as H2.
        rewrite /syncIR in H2.
        smt ~no_macros.
      }
      (* We apply the induction hypothesis. *)
      have IH0 := IH (if i = ind_one then init else I(ind_pred i)) 3 _. left. smt ~no_macros.
      clear IH.
      simpl.

      have -> : RKRreceive@R i = RKIsend@(if i = ind_one then init else I(ind_pred i)).
         {
         case i = ind_one; intro H.
         + rewrite if_true //. 
           rewrite -SyncIR_init; [1: smt ~no_macros | 2: auto].
         + rewrite if_false //.
           rewrite -SyncIR2 ; [1: auto | 2,3: smt ~no_macros].

         }
       apply (ded_right fst). simpl. 
       rewrite /Secret_prop /Secret_target in IH0.
       have DedNIH := IH0 _ n n2 _.
          right.  left. 
          case i=ind_one. 
           ++ intro Eq. 
            localize H1 as H1'.
            rewrite /getIi.  
           smt ~no_macros. 
         ++ intro Neq. by rewrite /getIi.

      case i=ind_one. 
        ++ by rewrite if_true //. 
        ++ by rewrite if_false. 
      clear IH0.
      rewrite if_false in DedNIH; 1: by smt ~no_macros.
      rewrite if_true in DedNIH; 1: by smt ~no_macros.

      rewrite /Oracles /Opublic expand_ORKRreceive in DedNIH. by apply DedNIH. 


  - rewrite not_or not_and not_and in H1.

      (* `HealthyR i` and `not(HealthyI (i-1))` together imply that
         `gI i@R i = g^(b (ind_pred i))`, so `gSendR` is `g^b (i-1) ** a i`.
         Lemmas `Secret_UnsyncR` proves that under these conditions,
         the oracles cannot deduce `g^b (i-1) ** a i` *)

      apply ded_right (fun x => (snd x)).
      rewrite /=.
      have [sR sI _ -> _] := Heal_DHpubR i _ _ _ _; 1,2,3,4:auto. 
       
      rewrite -expand_ORKRreceive.  
      rewrite /Secret_prop /Secret_target in IH.
      have IH0 := IH (R i) 0 _ _ i (ind_pred i).  constraints.  smt ~no_macros.

      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_true in IH0; 1: by smt ~no_macros.

      rewrite /Oracles /Opublic E_com sR sI in IH0.  
      by apply IH0.  

  (**********************************)
  (* Case 3.1.2: taur=I i is maximum *)
  (**********************************)

  (* Transposition of case 3.1.1 *)
  * rewrite /Secret_prop /Secret_target.
    intro Hap1 n n2 Heal.
    rewrite Htau in *.
    clear Htau Hap1.

    (* we quickly take care of the value of the case if `side` is not 2. *)
   ghave [I | I] : [side=4 || not(side=4)]; 1: rewrite or_comm -impl_charac; intro _; assumption.
    {
      rewrite if_true; 1:  smt ~no_macros.
      rewrite /getRi   in Heal.
      rewrite /RKRsend.  
      rewrite /Secret_prop /Secret_target in IH.
      have IH0 := IH (pred (I i)) side _ _ n n2 _. smt ~no_macros. constraints. by left. 
      by rewrite if_true in IH0; 1: by smt ~no_macros.   
    }

    ghave I1 : [side=3]; 1: by smt ~no_macros. 

    rewrite I1 /= in *.
    clear I.

    rewrite /getIi in Heal.  
    rewrite /RKIsend.
    rewrite /Oracles /Opublic.

    rewrite expand_ORKIreceive.

    prf ~right ~under_hash 0. {
      (* Most cases are solved with a non-collision lemma. *)
      repeat split.
      - (* `RKIreceive@I i <> RKIsend@I i0` *)
        have H : RKIreceive@I i <> RKIsend@pred(I i); 2: auto.
        rewrite neq_sym.
        apply NoColRKIsendRKIreceive.
        constraints.
      - (* `RKIreceive@I i <> RKIsend@I i0` *)
        intro j O _ F.
        apply (f_apply fst) in F.
        rewrite /= .
        by have _ := NoColRKIsendRKIreceive (pred (I j)) (I i); [1:constraints].

      - (* `RKIreceive@I i <> RKIsend@init` *)
        simpl.
        intro F.
        apply (f_apply fst) in F.
        rewrite /= in F.
        have H := NoColRKIreceiveIzero i _; 1: auto.
        smt.
      - (* Here, we prove the the attacker cannot deduce `gSendI i@I i` before
           the action `I i` due to the freshness of `b i`. *)
        intro j I. 
        have I0 : RO j < I i. { 
          repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); constraints.
        }
        clear I Hap.
        intro Ded.
        (* `Ded` implies that `frame@pred RO j |> gSendI i@I i`.
            However `gSendI i@I i = x ^ b i` with `x` known by the attacker
            at `pred (I i)` and `b i` fresh before `I i`.
            So, we rewrite `Ded` to have `Ded : b i = y` with `b i` fresh in `y` *)
        apply f_apply (fun x => dlog (toG (snd x))) in Ded.
        rewrite /gSendI /gR /= E_com in Ded.
        apply mult_inv_l in Ded.
        fresh Ded => //; smt ~no_macros.
      - (* `RKIreceive@I i <> RKRsend@R j` if `R j` happens before `I i`. *)
        simpl.
        intro i0 I.
        have I0 : R i0 < I i. { 
          repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); constraints.
        }
        simpl. lemmas.
        by have H := NoColRThenI i i0 _; [1:constraints].
      - (* `RKIreceive@I i <> RKRreceive@R i0` *)
        simpl.
        intro j L. 
        have I0 : R j < I i. {
          repeat (destruct L as [[i1 X]|L] + destruct L as [_|L]); constraints.
        }
        by have NoCol := NoColRKRreceiveRKIreceive (R j) (I i) _; 1: constraints.
      - (* `RKIreceive@I i <> RKIsend@I j` *)
        simpl.
        intro j L F.
        have I0 : happens(I j, I i). {
          repeat (destruct L as [[i1 I]|L] + destruct L as [L|L]); try constraints.
           }
        apply (f_apply fst) in F.
        rewrite /= in F.
        by have NoCol := NoColRKIsendRKIreceive (pred (I j)) (I i) _; [1:constraints].

      - (* `RKIreceive@I i <> SK` *)
        simpl.
        intro I F.
        apply (f_apply fst) in F.
        rewrite /= in F.
        have H := NoColRKIreceiveIzero i _; 1: constraints.
        smt.
      - (* `RKIreceive@I i <> RKIreceive@I j` if `I j <> I i` *)
        simpl.
        intro j L.
        have I0 : I j < I i. {
          repeat (destruct L as [[i1 L]|L] + destruct L as [L|L]); try constraints.
          + destruct L as [L1 [L2 Sync]]. 
             (* `not SyncRI i1` with `i1<=i` implies `not (SyncIR i)`
                which contradicts `HealthyR i` *)
            localize Heal as Heal0.
            clear Heal IH Hap.
            case i=i1; smt ~no_macros.
        }
        by have _ := NoColRKIreceive i j _ _; [1:constraints].
    }
    simpl.

    (* either the first or the second element of the pair will be secret,
       depending on the following. *)
    ghave [H1|H1] : [ ( (HealthyI (ind_pred i) && not(SyncRI i)) || (HealthyR i && SyncRI i)) || 
                     not(((HealthyI (ind_pred i)  && not(SyncRI i)) || (HealthyR i && SyncRI i)))]
     ; 1: rewrite or_comm -impl_charac; intro _; assumption.
 
    - case H1.
      -- rewrite -expand_ORKIreceive.  

      rewrite /Secret_prop /Secret_target in IH.
      apply (ded_right fst). simpl.


      have IH0 := IH (I i) 1 _  _ n n2.  constraints.  smt ~no_macros.

      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_true in IH0; 1: by smt ~no_macros.
      rewrite /Oracles /Opublic in IH0. by apply IH0. 

      --
     (* use `SyncRI i` to rewrite `RKIreceive` into `RKRsend`,
         which is secret by induction and `HealthyR i` *)
      rewrite /Secret_prop /Secret_target in IH.
      destruct H1 as [H Sync]. rewrite -syncRI_to_SyncRI in Sync.
      (*First, we prove `R i < I i` with `SyncRI i`.*)
      have I : R i < I i. {
        rewrite /syncRI in Sync.
        smt ~no_macros.
      }
      (* We apply the induction hypothesis. *)
      have IH0 := IH (R i) 4 _ _ n n2 _; [1,3 : auto | 2: smt ~no_macros].
      simpl.
      clear IH.
      rewrite -SyncRI2 in IH0. auto. smt ~no_macros. 
      apply ded_right fst. simpl.
      rewrite /Oracles /Opublic in IH0.
      rewrite -expand_ORKIreceive. 
      by apply IH0.

    - 
      rewrite not_or not_and in H1.
      destruct H1 as [H1 H2].      

      apply ded_right (fun x => (snd x)).
      rewrite /=.
      have [sR sI _ -> _] := Heal_DHpubI i _ _ _ _; 1,2,3,4:auto. 
       
      rewrite -expand_ORKIreceive.  
      rewrite /Secret_prop /Secret_target in IH.
      have IH0 := IH (R i) 0 _ _ i i.  constraints.  smt ~no_macros.

      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_true in IH0; 1: by smt ~no_macros.

      rewrite /Oracles /Opublic sR sI in IH0.  
      by apply IH0.  

  (*************************************)
  (* Case 3.1.3: taur<>R/I i is maximum *)
  (*************************************)
* rewrite /Secret_prop /Secret_target in *.
  intro Hap2 n n2 H. 
  have -> : RKRsend@tau0 = RKRsend@pred tau0.
  {
    case tau0 => //.
    intro [i T].
    by have _ := Zt i.
  }

  have -> : RKIsend@tau0 = RKIsend@pred tau0.
  {
    case tau0 => //. 
    intro [i T].
    by have _ := Zt i.
  }
  have IH0 :=  IH (pred tau0) => {IH}. 
  
     have IH1 := IH0 side _ _ n n2 _ => {IH0}.  
    rewrite -getIi_notI. 
     {intro _ i U. by have _ := Zt i. }
     constraints.
    rewrite -getRi_notR. 
     {intro i. by have _ := Zt i. }
    constraints.
     by simpl.
     auto.  
     by left. 

    rewrite (if_false  (side = 2)) in *. smt ~no_macros. smt ~no_macros.
    rewrite (if_false  (side = 1)) in *. smt ~no_macros. smt ~no_macros.
    rewrite (if_false  (side = 0)) in *. smt ~no_macros. smt ~no_macros.
     by apply IH1.
Qed.


(*****************************************)
(* Case 3.2: taur is maximum, and side<3 *)
(*****************************************)	


(* We will have to eliminate the extra hash h produced by RKRreceive or
RKIreceive on the right hand side. *)


global lemma Secret_case3_2 @set:S/left (tau0:timestamp[const]):
  [init < tau0]
  ->
  (Forall (taur:timestamp[const], t:int[const]), [taur < tau0] ->
      (Secret_prop t (pred tau0) (pred tau0) tau0 (pred tau0) taur))
->
  (Forall (taur:timestamp[const], t:int[const]),  [taur < tau0 || (taur = tau0 && t < 3)] ->
      (Secret_prop t (pred tau0) (pred tau0) tau0 (pred tau0) taur)).
Proof.
 (* We prove the secrecy of RKRreceive/RKIreceive, only by using the past.*)
  intro Hap IH taur.  
  intro side Hap0. 
  ghave [H | H] : [taur < tau0 || taur = tau0]; 1: by simpl. {
    by apply IH.
  }
  
  rewrite H in *.
  ghave S : [side < 3]. by smt ~no_macros.
  clear H Hap0 taur.
  ghave [[i Htau] | [i Htau] | Zt] :
                             (Exists (i:index [const]), [tau0=R i]) 
                          \/ (Exists (i:index [const]), [tau0=I i]) 
                          \/ (Forall (i:index [const]), [tau0<>R i && tau0<>I i ]).
  * case tau0; try ((intro [j R] + intro j); right; right; intro j'; constraints).  
    + intro [i R]. left. by exists i.
    + intro [i I]. right. left. by exists i.

  (***********************************)
  (* Case 3.2.1: taur=R i is maximum *)
  (***********************************)

  * rewrite /Secret_prop /Secret_target.
    intro Hap1 n n2 Heal.
    rewrite Htau in *.
    clear Htau Hap1.
    (* we quickly take care of the value of the case if `side` is for I. *)
    ghave [Si | Si] : [ (side=1 || side=0) || side =2]; 1: by smt ~no_macros. {
      rewrite if_false; 1: by smt ~no_macros.
      rewrite (if_false (side=3)); 1: by smt ~no_macros.
      rewrite (if_false (side=2)); 1: by smt ~no_macros.
      rewrite /getIi   in Heal.
      rewrite /RKIreceive.
      rewrite /Secret_prop /Secret_target in IH.
      have IH0 := IH (pred (R i)) side _ _ n n2 _. smt ~no_macros. constraints. constraints.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      by rewrite if_false in IH0; 1: by smt ~no_macros.
    }
    rewrite (if_false); 1: by smt ~no_macros.
    rewrite (if_false); 1: by smt ~no_macros.
    rewrite (if_true); 1: by smt ~no_macros.


    rewrite /getRi in Heal.  
    rewrite /RKRreceive.
    rewrite /Oracles /Opublic.

    rewrite expand_ORKRreceive.

    ghave [Hl Hs] : [HealthyR (ind_pred i) && not (SyncIR (ind_pred i))]. smt ~no_macros.
     (* We have RKIsend@I (i-1) <> RKRreceive@R i *) 
    clear Heal.

    prf ~right ~under_hash 0.
    + { (* first subgoal: phi_prf *)
        repeat split.
        ++   intro j L H Eq.
             have I0 : R j < R i. smt ~no_macros.
             have _ : RKRreceive@R i = RKRreceive@R j. auto.     
             by have _ := NoColRKRreceive i j _ _. 
        ++ intro Eq. have _ : RKIsend@init =RKRreceive@R i by auto.
           by have _ := NoColRKRreceiveRKIsend i init.
        ++ intro j L. 
           have I0 : RO j < R i. 
            { repeat (destruct L as [[i1 _]|L] + destruct L as [_|L]); 
              try constraints.
            }
           clear Si.  
           rewrite /input.
           intro Ded.
           apply (f_apply fst) in Ded.              
           simpl. 
           (* HP says: oracles@pred t0, t0, t0 *> secret@R i *)
           have ZIH := (IH (pred (R i)) 4 _); 1:auto.
           
           (* then SecretEarlier to get RO' j instead of t0/pred t0 *)
           have DedNIH :=
             Secret_earlier (pred (R i)) (RO j) 
                            (pred (R i)) (RO j)
                            (R i) (RO j)
                            (pred (R i)) (RO j)
                            (pred (R i)) 4
                            _ _ _ _ ZIH;
             [1,2,3,4:constraints].
           rewrite /Secret_prop /Secret_target in DedNIH.
           have NDed  := DedNIH _ n n2 _ => {DedNIH}.
         
           left. simpl.  by rewrite getRi_pred. auto. 
           apply if_true_ded in NDed; [1: auto]. 
           have DedF := DeduceFrame (pred (RO j)) (RO j) _; 1:constraints. 
           
           apply (no_ded_ded _ _ _ NDed) in DedF => {NDed}.
           rewrite /( *>) in DedF.
           by have _ := DedF (fun m => fst (att m)).
        ++   intro j L.
             have I0 : R j < R i.
                  { 
                    repeat (destruct L as [[i1 X]|L] + destruct L as [_|L]);
                    try constraints.
                  }
               by have _ := NoColRKRreceive i j _ _. 
        ++ intro j L. 
                 have I0 : R j < R i.
                  { repeat (destruct L as [[i1 X]|L] + destruct L as [_|L]);
                    try constraints.
                  }
           by have _ := NoColRKRsendRKRreceive (pred (R i)) (R j) _.
        ++   intro j L. 
              have I0 : I j < R i. 
              { repeat (destruct L as [[i1 _]|L] + destruct L as [_|L]);
                constraints.
              }
           by have _ := NoColRKRsendRKIsend (pred (R i)) (pred (I j)) _; [1:constraints].
        ++ intro _ Eq. have _ : RKIsend@init =RKRreceive@R i by auto.
           by have _ := NoColRKRreceiveRKIsend i init; [1:constraints].
        ++ intro _ L Eq. have _ : RKIsend@I i0 = RKRreceive@R i. smt. 
              have I0 : happens(I i0, R i). 
              { repeat (destruct L as [[i1 _]|L] + destruct L as [_|L]);
                try constraints.
              }
           by have _ := NoColRKRreceiveRKIsend i (I i0) _ _; [1:constraints].
    }
   +
      rewrite -expand_ORKRreceive.  

      rewrite /Secret_prop /Secret_target in IH.
      apply (ded_right fst). simpl.
      clear Si.

      have IH0 := IH (pred (R i)) 4 _ _ n n2 _. by rewrite getRi_pred.  constraints.  smt ~no_macros.

      rewrite if_true in IH0; 1: by smt ~no_macros.
      rewrite /Oracles /Opublic in IH0. by apply IH0. 

  (***********************************)
  (* Case 3.2.2: taur=I i is maximum *)
  (***********************************)


*   rewrite /Secret_prop /Secret_target.
    intro Hap1 n n2 Heal.
    rewrite Htau in *.
    clear Htau Hap1.
    (* we quickly take care of the value of the case if `side` is for I. *)
    ghave [Is | Is] : [(side=2 || side=0) || side=1]; 1: by smt ~no_macros. {
      rewrite if_false; 1: by smt ~no_macros.
      rewrite (if_false (side=3)); 1: by smt ~no_macros.
      rewrite (if_false (side=1)); 1: by smt ~no_macros.
      rewrite /getRi   in Heal.
      rewrite /RKRreceive.
      rewrite /Secret_prop /Secret_target in IH.
      have IH0 := IH (pred (I i)) side _ _ n n2 _. smt ~no_macros. constraints. constraints.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_false in IH0; 1: by smt ~no_macros.
      by rewrite (if_false (side=1)) in IH0; 1: by smt ~no_macros.
    }
    rewrite (if_false); 1: by smt ~no_macros.
    rewrite (if_false); 1: by smt ~no_macros.
    rewrite (if_false); 1: by smt ~no_macros.
    rewrite if_true. by simpl.

    rewrite /getIi in Heal.  
    rewrite /RKIreceive.
    rewrite /Oracles /Opublic.

    rewrite expand_ORKIreceive.

    ghave [Hl Hs] : [ HealthyI (ind_pred i) && not (SyncRI i)]. smt ~no_macros.
     (* We have RKIsend@I (i-1) <> RKRreceive@R i *) 
    clear Heal.

    prf ~right ~under_hash 0.
    + { (* first subgoal: phi_prf *)
        repeat split.
        ++   intro j I H Eq.
             have I0 : I j < I i. smt ~no_macros.
             have _ : RKIreceive@I i = RKIreceive@I j. auto.     
             by have _ := NoColRKIreceive i j _ _; [1:constraints].
        ++ intro Eq. have _ : RKIreceive@I i =RKIsend@init by auto.             
            by have _ := NoColRKIsendRKIreceive init (I i); [1:constraints].

        ++ intro j I. 
           have I0 : RO j < I i. 
            { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]); 
              try constraints.
            }
           clear I.  
           rewrite /input.
           intro Ded.
           apply (f_apply fst) in Ded.              
           simpl. 
           (* HP says: oracles@pred t0, t0, t0 *> secret@R i *)
           have ZIH := (IH (pred (I i)) 3 _); 1:auto.
           
           (* then SecretEarlier to get RO' j instead of t0/pred t0 *)
           have DedNIH :=
             Secret_earlier (pred (I i)) (RO j) 
                            (pred (I i)) (RO j)
                            (I i) (RO j)
                            (pred (I i)) (RO j)
                            (pred (I i)) 3
                            _ _ _ _ ZIH;
             [1,2,3,4:constraints].
           rewrite /Secret_prop /Secret_target in DedNIH.
           have NDed  := DedNIH _ n n2 _ => {DedNIH}.
           right. left. simpl.  by rewrite getIi_pred. auto. 
           apply if_false_ded in NDed; [1: auto]. 
           apply if_true_ded in NDed; [1: auto]. 
           have DedF := DeduceFrame (pred (RO j)) (RO j) _; 1:constraints. 
           
           apply (no_ded_ded _ _ _ NDed) in DedF => {NDed}.
           rewrite /( *>) in DedF.
           by have _ := DedF (fun m => fst (att m)).
        ++   intro j I. 
              have I0 : R j < I i. 
              { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                constraints.
              }
           by have _ := NoColRKRsendRKIsend (pred (R j)) (pred (I i)) _; [1:constraints].
        ++ intro _ I Eq. have _ : RKRsend@R i0 = RKIreceive@I i. smt. 
              have I0 : happens(R i0, I i). 
              { repeat (destruct I as [[i1 _]|I] + destruct I as [_|I]);
                try constraints.
              }
              by have _ := NoColRKIreceiveRKRsend i0 i _ _; [1:constraints].
        ++   intro j I.
             have I0 : I j < I i.
                  { 
                    repeat (destruct I as [[i1 X]|I] + destruct I as [_|I]);
                    try constraints.
                  }
               by have _ := NoColRKIreceive i j _ _; [1:constraints].
        ++ intro _ Eq. have _ : RKIreceive@I i =RKIsend@init by auto.             
            by have _ := NoColRKIsendRKIreceive init (I i); [1:constraints].
        ++ intro j L. 
                 have I0 : I j < I i.
                  { repeat (destruct L as [[i1 X]|L] + destruct L as [_|L]);
                    try constraints.
                  }
           by have _ := NoColRKIsendRKIreceive (pred (I i)) (I j) _; [1:constraints].
    }
   +
      rewrite -expand_ORKIreceive.  

      rewrite /Secret_prop /Secret_target in IH.
      apply (ded_right fst). simpl.

      have IH0 := IH (pred (I i)) 3 _ _ n n2 _. by rewrite getIi_pred.  constraints.  smt ~no_macros.

      rewrite if_false in IH0; 1: by smt ~no_macros.
      rewrite if_true in IH0; 1: by smt ~no_macros.
      rewrite /Oracles /Opublic in IH0. by apply IH0. 

  (**************************************)
  (* Case 3.2.2: taur<>I/R i is maximum *)
  (**************************************)

*  rewrite /Secret_prop /Secret_target in *.
  intro Hap2 n n2 H.
  have [-> -> -> ->] : RKRsend@tau0 = RKRsend@pred tau0 && RKRreceive@tau0 = RKRreceive@pred tau0
               && RKIsend@tau0 = RKIsend@pred tau0 && RKIreceive@tau0 = RKIreceive@pred tau0.
  {
    case tau0 => //.
    intro [i T].
    by have _ := Zt i.
    intro [i T].
    by have _ := Zt i.
  }

  have IH0 :=  IH (pred tau0) side _ _ n n2 _ => {IH}. 
 
    rewrite -getIi_notI. 
     {intro _ i U. by have _ := Zt i. }
     constraints.
    rewrite -getRi_notR. 
     {intro i. by have _ := Zt i. }
    constraints.
     by simpl.
     auto.  
     auto.
    
     by apply IH0.
Qed.
