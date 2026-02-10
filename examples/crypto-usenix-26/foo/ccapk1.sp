include Core.
include Libs.
include Games.
include[admit] processes.


axiom [any] len_zero_enc1_0_A (s:bsigned) : 
len 
(<(comm v0 kc0),
 format (unblind (comm v0 kc0) (read (att' rdAdmin)) tkA s)> )
= 
len zero_enc1 .

axiom [any] len_zero_enc1_1_A (s:bsigned) : 
len 
(<(comm v1 kc1),
 format (unblind (comm v1 kc1) (read (att' rdAdmin)) tkA s)> )
= 
len zero_enc1 .

axiom [any] len_zero_enc1_1_B (s:bsigned) : 
len 
(<(comm v1 kc1),
 format (unblind (comm v1 kc1) (read (att' rdAdmin)) tkB s)> )
= 
len zero_enc1.

axiom [any] len_zero_enc1_0_B (s:bsigned) : 
len 
(<(comm v0 kc0),
 format (unblind (comm v0 kc0) (read (att' rdAdmin)) tkB s)> )
= 
len zero_enc1.






(*******************************************************************************
## Processes : rewriting encryption in first phase
********************************************************************************)

process Voter_CCA_pk1
  (cm : message) (pkAdmin : pk_sign)  
  (kc : k_comm) (tk : token_bsign) 
  (seed_enc0, seed_enc1 : seed) 
= 
  let b  = blind cm pkAdmin tk in
  $auth : out(c,format b);

  in(c,sb);
  let sb     = read sb in
  let acc    = baccepte cm pkAdmin tk sb in
  let ub     = unblind  cm pkAdmin tk sb in
  $vote : out (c,  if acc then
  format (encr (diff((<cm,format ub>), zero_enc1))
          (pk_enc sk_mix1) seed_enc0));

  in (c,setBB);
  lock mutex_BB;
  let voted = mem_bb (cm,ub) BB in
  let i = find_bb (cm,ub) BB in
  unlock mutex_BB;
  $opening : out(c,  if acc && voted then
  format (encr ((<format i,format kc>))
         (pk_enc sk_mix2) seed_enc1)). 


process Alice_CCA_pk1 (cm:message) (kcA : k_comm) (pkAdmin : pk_sign) = 
  Voter_CCA_pk1(cm, pkAdmin, kcA, tkA, seedA_enc1, seedA_enc2).

process Bob_CCA_pk1 (cm:message) (kcB : k_comm) (pkAdmin : pk_sign) =
  Voter_CCA_pk1(cm, pkAdmin, kcB, tkB, seedB_enc1, seedB_enc2).

process mixer_vote_collect_CCA_pk1 
(cmA : message) (cmB : message) 
(pkAdmin : pk_sign) 
= 
  !_i ( 
    in(c,m);
    let m   = read m in
    let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
    let ubB =  unblind cmB pkAdmin tkB (read (input@Bvote))  in
    let acc_A =  baccepte cmA pkAdmin tkA (read (input@Avote))  in
    let acc_B =  baccepte cmB pkAdmin tkB (read (input@Bvote))  in
    box(i):= 
      if Avote < MVC(i) 
      && m = encr (diff((<cmA,format ubA>),zero_enc1)) (pk_enc sk_mix1) seedA_enc1 
      then ( <cmA,format ubA>)
      else if Bvote < MVC(i) 
      && m = encr (diff((<cmB,format ubB>),zero_enc1)) (pk_enc sk_mix1) seedB_enc1           
           then (<cmB,format ubB>)
           else  decr m sk_mix1
  ).

process mixer_open_collect_CCA_pk1
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
    count(j) := 
      if m = encr (<format iA, format kcA>) (pk_enc sk_mix2) seedA_enc2 
      then  (<format iA, format kcA>)
      else if  m = encr (<format iB, format kcB>) (pk_enc sk_mix2) seedB_enc2 
           then ( <format iB, format kcB>)
           else decr m sk_mix2;
    unlock mutex_BB;
    unlock mutex_count
  ).

process mixer_open_publish_CCA_pk1 
(pkAdmin : pk_sign) (cmA,cmB : message)
(kcA, kcB: k_comm)  
= 
  let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
  let ubB = unblind cmB pkAdmin tkB (read (input@Bvote)) in
  lock mutex_BB;
  lock mutex_count;
  lock mutex_box;
  let iA = find_bb (cmA,ubA) BB in
  let iB = find_bb (cmB,ubB) BB in
  let votedA = mem_bb (cmA,ubA) BB in
  let votedB = mem_bb (cmB,ubB) BB in
  let accA    = baccepte cmA pkAdmin tkA (read (input@Avote)) in
  let accB   = baccepte cmB pkAdmin tkB (read (input@Bvote)) in
  (* let mA1 = diff(if accA then <cmA, format ubA>, zero) in  *)
  (* let mB1 = diff(if accB then <cmB, format ubB>, zero) in *)
  let mA2 =  <format iA, format kcA> in
  let mB2 =  <format iB, format kcB> in
  let Count = fun i => count i in
  let Box   = fun i => box   i in
  unlock mutex_BB;
  unlock mutex_count;
  unlock mutex_box;
  let commAB = 
    (exists i, happens(MVC(i)) && Avote < MVC(i) &&
       (input@MVC(i)) = 
        format (encr (diff(<cmA, format ubA>, zero_enc1)) (pk_enc sk_mix1) seedA_enc1)) 
    &&
    (exists i, happens(MVC(i)) && Bvote < MVC(i) &&
       (input@MVC(i)) = 
       format (encr ( diff(<cmB, format ubB>, zero_enc1)) (pk_enc sk_mix1) seedB_enc1)) 
    && accA
    && accB
  in
  let voteAB =
    (exists i, happens(MOC(i)) &&
        (input@MOC(i)) =
        format (encr mA2 (pk_enc sk_mix2) seedA_enc2)) 
    &&
    (exists i, happens(MOC(i)) &&
       (input@MOC(i)) = 
       format (encr mB2 (pk_enc sk_mix2) seedB_enc2))
   && votedA
   && votedB 
  in
  let votes = shuffle Count in
  out(c, if (commAB && voteAB) then if partial_injective Count (fun i => MOC(i)) then votes).   


system Privacy_Left_CCA_pk1 = 
   let vA  = v0 in
   let vB  = v1 in 
   let kcA = kc0 in
   let kcB = kc1 in
   let cmA = comm vA kcA in
   let cmB = comm vB kcB in
   Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
   ( (A   : Alice_CCA_pk1 (cmA,kcA,pkAdmin)                     )
   | (B   : Bob_CCA_pk1   (cmB,kcB,pkAdmin)                     ) 
   | (MVC : mixer_vote_collect_CCA_pk1 (cmA,cmB,pkAdmin)        )
   | (MVP : mixer_vote_publish                                  )
   | (BBS : set_BB                                              )
   | (MOC : mixer_open_collect_CCA_pk1 (cmA,cmB,kcA,kcB,pkAdmin))
   | (MOP : mixer_open_publish_CCA_pk1 (pkAdmin,cmA,cmB,kcA,kcB))
 ).

(* compatibility check *)
global lemma [Privacy_real/left,Privacy_Left_CCA_pk1/left] _ : [true].
Proof. auto. Qed.

global lemma [Privacy_Left_CCA_pk1] Left_CCA_pk1 (t:_[const]) : 
  [happens(t)] -> equiv(frame@t). 
Proof. 
 intro *.
 crypto ~no_subgoal_on_failure ~time_sensitive CCA2 (key:sk_mix1).
 - smt ~no_macros.
 - smt ~no_macros.
 - smt ~no_macros. 
 - intro *.
   destruct H0 as 
     [[h0 h1 h2] h3 h4 h5 [h6 h7 h8] h9 h10 h11 ].
   have h0i0 := h0 i0.
   have h6i := h6 i.
   clear h0 h1 h6 h7 h2 h5 h8.
   rewrite h3 h4 h9 h10 h11 in *.
   clear h4 h9 h10 . simpl.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2] h3 h4 h5 [h6 h7 h8 h9] h10 h11 h12 h13].
   rewrite ?h7 in *.
   have h7i := h7 i.
   rewrite h3 h4 h5 ?h8 ?h9 ?h10 ?h11 h12 h13 in *.   
   use Trace.any_MOP.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2] h3 h4 h5 [h6 h7] h8 h9].
   rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 ?h6 ?h7 ?h8 ?h9  in *. 
   simpl.
   clear h0 h1 h4 h5 h6 h7 h8 h9.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 [h7 h8 h9 h10] h11 h12 h13].
   have h0i0 := h0 i0.
   have h7i := h7 i. 
   rewrite 
     ?h3 ?h4 ?h5 ?h6  ?h8 ?h9  ?h11 ?h12  in *.
   simpl.
   rewrite forall_true1 in *.
   simpl.
   use (lt_index_total i i0).
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 [h7 h8] h9 h10].
   clear h0 h1 h2 h5 h7 h10.
   have hi := h8 i. clear h8.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 h7 [h8 h9 h10 h11] h12 h13 h14 h15 ].
   have hi0:= h0 i0.
   have hi := h8 i.
   rewrite  h1 h2 h3 ?h4 ?h5 h6 h7  h11 ?h12 ?h13 h14 h15 in *.
   use (lt_index_total i i0).
   clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10  h12 h13.
   simpl.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 h7 [h8 h9] h10 h11 ].
   rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 h6 h7 ?h8 ?h9 h10 h11 in *.
   smt ~no_macros.
 - auto.
 - auto.    
 - intro *.
   apply len_zero_enc1_0_A. 
 - intro *.
   apply len_zero_enc1_1_B.  
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7] h8 h9].
   rewrite h1 h2 h3 h4  in *. simpl.
   apply h3.
   have Hformat := format_inj[ctxt].
   simpl.
   apply Hformat. rewrite Meq. by project. (* XXX who does smt fail here? *)
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7] h8 h9].
   rewrite h1 h2 h3 h4  in *. simpl.
   apply h1.
   have Hformat := format_inj[ctxt]. 
   simpl.
   apply Hformat. rewrite Meq. by project.
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7] h8 h9 h10].
   rewrite h1 h2 h3 h4  in *. simpl.
   apply h3.
   have Hformat := format_inj[ctxt].
   simpl. apply Hformat. rewrite Meq. by project.
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7] h8 h9].
   rewrite h1 h2 h3 h4  in *. simpl.
   apply h1.
   have Hformat := format_inj[ctxt].
   simpl. apply Hformat. rewrite Meq. by project.
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7 h8 h9] h10 h11 h12 h13].
   by have ?:= Trace.any_MOP (MVC(i)).
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7 h8 h9] h10 h11 h12 h13].
   by have ?:= Trace.any_MOP (MVC(i)).
- intro *.
  destruct H0 as [h0 h1 h2].
  destruct H1 as [h3 h4 h5 [h6 h7] h10 h11 h12].
  simpl.
  apply h3.
   have Hformat := format_inj[ctxt].
   simpl. apply Hformat. rewrite Meq. by project.
- intro *.
  destruct H0 as [h0 h1 h2].
  destruct H1 as [h3 h4 h5 [h6 h7] h10 h11 h12].
  simpl.
  apply h1.
  have Hformat := format_inj[ctxt].
  simpl. apply Hformat. rewrite Meq. by project.  
- intro *.
  apply len_zero_enc1_0_A.
- intro *.
  apply len_zero_enc1_1_B.
- intro *.
  apply len_zero_enc1_1_B.
- intro *.
  apply len_zero_enc1_0_A.
Qed.

system Privacy_Right_CCA_pk1 = 
   let vA  = v1 in
   let vB  = v0 in 
   let kcA = kc1 in
   let kcB = kc0 in
   let cmA = comm vA kcA in
   let cmB = comm vB kcB in
   Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
   ( (A   : Alice_CCA_pk1 (cmA,kcA,pkAdmin)                      )
   | (B   : Bob_CCA_pk1   (cmB,kcB,pkAdmin)                      ) 
   | (MVC : mixer_vote_collect_CCA_pk1 (cmA,cmB,pkAdmin)         )
   | (MVP : mixer_vote_publish                                   )
   | (BBS : set_BB                                               )
   | (MOC : mixer_open_collect_CCA_pk1 (cmA,cmB,kcA,kcB,pkAdmin) )
   | (MOP  : mixer_open_publish_CCA_pk1 (pkAdmin,cmA,cmB,kcA,kcB))
 ).

(* compatibility check *)
global lemma [Privacy_real/left,Privacy_Right_CCA_pk1/left] _ : [true].
Proof. auto. Qed.

global lemma [Privacy_Right_CCA_pk1] Right_CCA_pk1 (t:_[const]) : 
[happens(t)] -> equiv(frame@t). 
Proof. 
 intro *.
 crypto ~no_subgoal_on_failure ~time_sensitive CCA2 (key:sk_mix1).
 - smt ~no_macros.
 - smt ~no_macros.
 - smt ~no_macros. 
 - intro *.
   destruct H0 as 
     [[h0 h1 h2] h3 h4 h5 [h6 h7 h8] h9 h10 h11 ].
   have h0i0 := h0 i0.
   have h6i := h6 i.
   clear h0 h1 h6 h7 h2 h5 h8.
   rewrite h3 h4 h9 h10 h11 in *.
   clear h4 h9 h10 . simpl.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2] h3 h4 h5 [h6 h7 h8 h9] h10 h11 h12 h13].
   rewrite ?h7 in *.
   have h7i := h7 i.
   rewrite h3 h4 h5 ?h8 ?h9 ?h10 ?h11 h12 h13 in *.   
   use Trace.any_MOP.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2] h3 h4 h5 [h6 h7] h8 h9].
   rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 ?h6 ?h7 ?h8 ?h9  in *. 
   simpl.
   clear h0 h1 h4 h5 h6 h7 h8 h9.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 [h7 h8 h9 h10] h11 h12 h13].
   have h0i0 := h0 i0.
   have h7i := h7 i. 
   rewrite 
     ?h3 ?h4 ?h5 ?h6  ?h8 ?h9  ?h11 ?h12  in *.
   simpl.
   rewrite forall_true1 in *.
   simpl.
   use (lt_index_total i i0).
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 [h7 h8] h9 h10].
   clear h0 h1 h2 h5 h7 h10.
   have hi := h8 i. clear h8.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 h7 [h8 h9 h10 h11] h12 h13 h14 h15 ].
   have hi0:= h0 i0.
   have hi := h8 i.
   rewrite  h1 h2 h3 ?h4 ?h5 h6 h7  h11 ?h12 ?h13 h14 h15 in *.
   use (lt_index_total i i0).
   clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10  h12 h13.
   simpl.
   smt ~no_macros.
 - intro *.
   destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 h7 [h8 h9] h10 h11 ].
   rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 h6 h7 ?h8 ?h9 h10 h11 in *.
   smt ~no_macros.
 - auto.
 - auto.    
 - intro *.
   apply len_zero_enc1_1_A.
 - intro *.
   apply len_zero_enc1_0_B.  
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7] h8 h9].
   rewrite h1 h2 h3 h4  in *. simpl.
   apply h3.
   have Hformat := format_inj[ctxt].
   simpl.
   apply Hformat. rewrite Meq. by project. (* XXX who does smt fail here? *)
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7] h8 h9].
   rewrite h1 h2 h3 h4  in *. simpl.
   apply h1.
   have Hformat := format_inj[ctxt]. 
   simpl.
   apply Hformat. rewrite Meq. by project.
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7] h8 h9 h10].
   rewrite h1 h2 h3 h4  in *. simpl.
   apply h3.
   have Hformat := format_inj[ctxt].
   simpl. apply Hformat. rewrite Meq. by project.
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7] h8 h9].
   rewrite h1 h2 h3 h4  in *. simpl.
   apply h1.
   have Hformat := format_inj[ctxt].
   simpl. apply Hformat. rewrite Meq. by project.
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7 h8 h9] h10 h11 h12 h13].
   by have ?:= Trace.any_MOP (MVC(i)).
 - intro *.
   destruct H0 as [h0 h1 h2].
   destruct H1 as [h3 h4 h5 [h6 h7 h8 h9] h10 h11 h12 h13].
   by have ?:= Trace.any_MOP (MVC(i)).
- intro *.
  destruct H0 as [h0 h1 h2].
  destruct H1 as [h3 h4 h5 [h6 h7] h10 h11 h12].
  simpl.
  apply h3.
   have Hformat := format_inj[ctxt].
   simpl. apply Hformat. rewrite Meq. by project.
- intro *.
  destruct H0 as [h0 h1 h2].
  destruct H1 as [h3 h4 h5 [h6 h7] h10 h11 h12].
  simpl.
  apply h1.
  have Hformat := format_inj[ctxt].
  simpl. apply Hformat. rewrite Meq. by project.  
- intro *.
  apply len_zero_enc1_1_A.
- intro *.
  apply len_zero_enc1_0_B.
- intro *.
  apply len_zero_enc1_0_B.
- intro *.
  apply len_zero_enc1_1_A.
Qed.

