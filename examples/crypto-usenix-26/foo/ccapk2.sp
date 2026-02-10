include Core.
include Libs.
include Games.
include[admit] processes.


axiom [any] len_zero_enc2_0 (i:index) : 
len 
(< format i, format kc0> )
= 
len zero_enc2.

axiom [any] len_zero_enc2_1 (i:index) : 
len 
(<format i, format kc1> )
= 
len zero_enc2.

(*******************************************************************************
## Processes : rewriting encryption in second phase
********************************************************************************)
process Voter_CCA_pk2
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
  $vote : out (c, if acc then 
  format (encr zero_enc1 (pk_enc sk_mix1) seed_enc0));

  in (c,setBB);
  lock mutex_BB;
  let voted = mem_bb (cm,ub) (BB@BBS) in
  let i = find_bb (cm,ub) (BB@BBS) in
  unlock mutex_BB;
  $opening : out(c, if acc && voted then
  format (encr (diff((<format i,format kc>),zero_enc2))
         (pk_enc sk_mix2) seed_enc1)). 



process Alice_CCA_pk2 (cm:message) (kcA : k_comm) (pkAdmin : pk_sign) = 
  Voter_CCA_pk2(cm, pkAdmin, kcA, tkA, seedA_enc1, seedA_enc2).

process Bob_CCA_pk2 (cm:message) (kcB : k_comm) (pkAdmin : pk_sign) =
  Voter_CCA_pk2(cm, pkAdmin, kcB, tkB, seedB_enc1, seedB_enc2).


process mixer_vote_collect_CCA_pk2
(cmA : message) (cmB : message) 
(pkAdmin : pk_sign) 
= 
  !_i ( 
    in(c,m);
    let m   = read m in
    let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
    let ubB =  unblind cmB pkAdmin tkB (read (input@Bvote))  in
    let accA =  baccepte cmA pkAdmin tkA (read (input@Avote))  in
    let accB =  baccepte cmB pkAdmin tkB (read (input@Bvote))  in
    lock mutex_box;
    box(i):= 
      if Avote < MVC(i) &&  m = encr (zero_enc1) (pk_enc sk_mix1) seedA_enc1 
      then ( <cmA,format ubA>)
      else if Bvote < MVC(i) && m = encr (zero_enc1) (pk_enc sk_mix1) seedB_enc1           
      then ( <cmB,format ubB>)
      else  decr m sk_mix1;
    unlock mutex_box
  ).



process mixer_open_collect_CCA_pk2 (cmA,cmB : message) 
(kcA,kcB : k_comm) 
(pkAdmin : pk_sign) =
  !_j(
    in(c,m);
    let m  = read m in
    let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
    let ubB = unblind cmB pkAdmin tkB (read (input@Bvote)) in
    lock mutex_BB;
    lock mutex_count;
    let iA = find_bb (cmA,ubA) (BB@BBS) in
    let iB = find_bb (cmB,ubB) (BB@BBS) in
    let votedA = mem_bb (cmA,ubA) (BB@BBS) in
    let votedB = mem_bb (cmB,ubB) (BB@BBS) in
    let accA    = baccepte cmA pkAdmin tkA (read (input@Avote)) in
    let accB   = baccepte cmB pkAdmin tkB (read (input@Bvote)) in
    count(j) := 
      if  m = encr diff((<format iA, format kcA>),zero_enc2) (pk_enc sk_mix2) seedA_enc2 
      then (<format iA, format kcA>)
      else if m = encr diff((<format iB, format kcB>),zero_enc2) (pk_enc sk_mix2) seedB_enc2 
           then (<format iB, format kcB>)
           else decr m sk_mix2;
    unlock mutex_BB;
    unlock mutex_count
  ).

process mixer_open_publish_CCA_pk2 
(pkAdmin : pk_sign) 
(cmA,cmB : message) 
(kcA,kcB : k_comm)
 =
  let ubA = unblind cmA pkAdmin tkA (read (input@Avote)) in
  let ubB = unblind cmB pkAdmin tkB (read (input@Bvote)) in
  let accA = baccepte cmA pkAdmin tkA (read (input@Avote)) in
  let accB = baccepte cmB pkAdmin tkB (read (input@Bvote)) in
  lock mutex_BB;
  lock mutex_count;
  lock mutex_box;
  let iA = find_bb (cmA,ubA) (BB@BBS) in
  let iB = find_bb (cmB,ubB) (BB@BBS) in
  let votedA = mem_bb (cmA,ubA) (BB@BBS) in
  let votedB = mem_bb (cmB,ubB) (BB@BBS) in
  let Count = fun i => count i in
  let Box   = fun i => box   i in
  unlock mutex_BB;
  unlock mutex_count;
  unlock mutex_box;
  let commAB =
      (exists i, happens(MVC(i)) && Avote < MVC(i) && (input@MVC(i)) =
        format (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1))  
   && (exists i, happens(MVC(i)) && Bvote < MVC(i) && (input@MVC(i)) = 
       format (encr zero_enc1 (pk_enc sk_mix1) seedB_enc1))
   && accA && accB
  in  
  let voteAB =
      (exists i, happens(MOC(i)) && (input@MOC(i)) =
        format (encr diff(<format iA, format kcA>,zero_enc2)  (pk_enc sk_mix2) seedA_enc2))  
   && (exists i, happens(MOC(i)) && (input@MOC(i)) = 
       format (encr diff(<format iB, format kcB>,zero_enc2) (pk_enc sk_mix2) seedB_enc2))
   && votedA && votedB
  in
  let votes = shuffle Count in
  out(c, if commAB && voteAB then 
         if partial_injective Count (fun i => MOC i) then votes).


system Privacy_Left_CCA_pk2 = 
   let vA  = v0 in
   let vB  = v1 in 
   let kcA = kc0 in
   let kcB = kc1 in
   let cmA = comm vA kcA in
   let cmB = comm vB kcB in
   Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
   ( (A   : Alice_CCA_pk2 (cmA,kcA,pkAdmin)                      )
   | (B   : Bob_CCA_pk2   (cmB,kcB,pkAdmin)                      ) 
   | (MVC : mixer_vote_collect_CCA_pk2 (cmA,cmB,pkAdmin)         )
   | (MVP : mixer_vote_publish                                   )
   | (BBS : set_BB                                               )
   | (MOC : mixer_open_collect_CCA_pk2 (cmA,cmB,kcA,kcB,pkAdmin) )
   | (MOP  : mixer_open_publish_CCA_pk2 (pkAdmin,cmA,cmB,kcA,kcB))
 ).

(* compatibility check *)
global lemma [Privacy_real/left,Privacy_Left_CCA_pk2/left] _ : [true].
Proof. auto. Qed.

(* set verboseCrypto = true. *)

global lemma [Privacy_Left_CCA_pk2] Left_CCA_pk2 (t:_[const]) : [happens(t,BBS)] -> equiv(frame@t). 
Proof.
intro *. 
crypto ~no_subgoal_on_failure CCA2 (key:sk_mix2).
- intro *.
  destruct H0 as
  [ [h0 h1 h2] h3 [h4 h5 h6] h7 ].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h6 ?h7  in *.
  simpl. 
  clear h1 h2 h5 h6.
  smt ~no_macros.

- intro *.
  destruct H0 as [ [h0 h1 h2] h3 [h4 h5 h6 h7] h8 h9 h10 h11 h12 h13].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 ?h6 ?h7 ?h8 h9 h10 h11 h12 h13 in *.
  simpl.
  clear h0 h2 h4 h6 h7 h8 h9 h10 h11 h12.
  smt ~no_macros.

- intro *.
  destruct H0 as [ [h0 h1 h2] h3 [h4 h5] h6 h7 h8].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 h6 ?h7 ?h8 in *.
  simpl.
  clear h0 h1 h5 h6 h7.
  smt ~no_macros.    

- intro *.
  destruct H0 as 
    [[h0 h1 h2] h3 h4 [h5 h6 h7] h8 h9].
  
  have h0i0 := h0 i0.
  have h5i := h5 i.
  rewrite  ?h1 ?h2 ?h3 ?h4 ?h6  ?h7 ?h8 ?h9 in *.
  simpl.
  clear h0 h1 h2 h3 h5 h6 h7 h8.
  smt ~no_macros. 

- intro *.
  destruct H0 as 
      [[h0 h1 h2] h3 h4 [h5 h6 h7 h8] h9 h10 h11 h12 h13 h14 h15].
  have h6i := h6 i.
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 ?h7 ?h8 ?h9 h10 h11 h12 h13 h14 h15 in *. 
  simpl.
  have hlt : MOC(i) <= pred MOP.
    { assert MOC(i) < MOP.
      by apply Trace.any_MOP (MOC(i)).
      constraints.
    }.
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15.
  smt ~no_macros.

- intro *.
  destruct H0 as 
     [[h0 h1 h2] h3 h4 [h5 h6] h7 h8 h9].
  have h5i := h5 i.
  rewrite ?h0 ?h1 ?h2 ?h4  ?h6 h7 ?h8 ?h9 in *.
  simpl.
  clear h0 h1 h5 h6 h7 h8.
  smt ~no_macros.

- intro *.
  destruct H0 as 
      [[h0 h1 h2] h3 h4 h5 h6 h7 h8 [h9 h10 h11 h12] h13 h14 h15 h16 h17 h18].
  rewrite ?h0 h1 ?h2 ?h3 h4 h5 h6 h7 h8 ?h9  h11 h12 ?h13 h14 h15 h16 h17 h18 in *.
  simpl.
  rewrite forall_true1 in *.
  simpl.
  have h0i0 := h0 i0. 
  have h9i := h9 i.
  have ? := lt_index_total i i0.
  clear h0 h1  h4 h5 h6 h7 h8 h9 h11 h12.
  smt ~no_macros.

- intro *.
  destruct H0 as 
      [[h0 h1 h2 h3] h4 h6 h7 h8 h9 h10 [h11 h12] h13 h14 h15].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4  ?h6 h7 h8 h9 h10 ?h11 ?h12 h13 ?h14 h15 in *.
  simpl.
  clear h0 h1 h2 h6 h7 h8 h9 h11 h14.
  smt ~no_macros.

- intro *.
  destruct H0 as 
  [[h0 h1 h2] h3 h4 h5 h6 h7 h8 h9 
   [h10 h11 h12 h13] h14 h15 h16 h17 h18 h19 h20].  
  rewrite ?h0 h1 ?h2 ?h3  h4 h5 h6 h7 h8 h9 
   ?h10  h12 h13 ?h14 h15 h16 h17 h18 h19 h20 in *.
  simpl.
  rewrite forall_true1 /= in *. 
  have h0i0 := h0 i0 => {h0}.
  have h10i := h10 i => {h10}.
  have ? := lt_index_total i i0.
  clear h1 h4 h5 h6 h7 h8 h9 h12 h13.
  smt ~no_macros.  

- intro *.
  destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 h7 h8 h9 h10 [ h11 h12] h13 h14 h15].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 h5 h6 h7 h8 h9 
   ?h10 ?h12 h13 h14 h15 in *. 
  simpl.
  clear h0 h1 h2 h5 h6 h7 h8 h9 h11 h14.
  smt ~no_macros.

- by intro *.
- by intro *.
- intro *.
  clear H0.  
  apply len_zero_enc2_0.
- intro *.
  clear H0.
  apply len_zero_enc2_1.
- intro *.
  destruct H0 as [h0 h1 h2].
  apply h0. 
  apply format_inj[ctxt].  
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h1.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h0.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h1.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h0.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h1.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.
- intro *.
  clear H0.  
  apply len_zero_enc2_0.
- intro *.
  clear H0.
  apply len_zero_enc2_1.
- intro *.
  clear H0.  
  apply len_zero_enc2_1.
- intro *.
  clear H0.
  apply len_zero_enc2_0.
Qed.


system Privacy_Right_CCA_pk2 = 
   let vA  = v1 in
   let vB  = v0 in 
   let kcA = kc1 in
   let kcB = kc0 in
   let cmA = comm vA kcA in
   let cmB = comm vB kcB in
   Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
   ( (A   : Alice_CCA_pk2 (cmA,kcA,pkAdmin)                      )
   | (B   : Bob_CCA_pk2   (cmB,kcB,pkAdmin)                      ) 
   | (MVC : mixer_vote_collect_CCA_pk2 (cmA,cmB,pkAdmin)         )
   | (MVP : mixer_vote_publish                                   )
   | (BBS : set_BB                                               )
   | (MOC : mixer_open_collect_CCA_pk2 (cmA,cmB,kcA,kcB,pkAdmin) )
   | (MOP  : mixer_open_publish_CCA_pk2 (pkAdmin,cmA,cmB,kcA,kcB))
 ).

global lemma [Privacy_Right_CCA_pk2] Right_CCA_pk2 (t:_[const]) : 
  [happens(t,BBS)] -> equiv(frame@t). 
Proof. 
intro *. 
crypto ~no_subgoal_on_failure CCA2 (key:sk_mix2).
- intro *.
  destruct H0 as
  [ [h0 h1 h2] h3 [h4 h5 h6] h7 ].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h6 ?h7  in *.
  simpl. 
  clear h1 h2 h5 h6.
  smt ~no_macros.

- intro *.
  destruct H0 as [ [h0 h1 h2] h3 [h4 h5 h6 h7] h8 h9 h10 h11 h12 h13].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 ?h6 ?h7 ?h8 h9 h10 h11 h12 h13 in *.
  simpl.
  clear h0 h2 h4 h6 h7 h8 h9 h10 h11 h12.
  smt ~no_macros.

- intro *.
  destruct H0 as [ [h0 h1 h2] h3 [h4 h5] h6 h7 h8].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 h6 ?h7 ?h8 in *.
  simpl.
  clear h0 h1 h5 h6 h7.
  smt ~no_macros.    

- intro *.
  destruct H0 as 
    [[h0 h1 h2] h3 h4 [h5 h6 h7] h8 h9].
  
  have h0i0 := h0 i0.
  have h5i := h5 i.
  rewrite  ?h1 ?h2 ?h3 ?h4 ?h6  ?h7 ?h8 ?h9 in *.
  simpl.
  clear h0 h1 h2 h3 h5 h6 h7 h8.
  smt ~no_macros. 

- intro *.
  destruct H0 as 
      [[h0 h1 h2] h3 h4 [h5 h6 h7 h8] h9 h10 h11 h12 h13 h14 h15].
  have h6i := h6 i.
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 ?h7 ?h8 ?h9 h10 h11 h12 h13 h14 h15 in *. 
  simpl.
  have hlt : MOC(i) <= pred MOP.
    { assert MOC(i) < MOP.
      by apply Trace.any_MOP (MOC(i)).
      constraints.
    }.
  clear h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15.
  smt ~no_macros.

- intro *.
  destruct H0 as 
     [[h0 h1 h2] h3 h4 [h5 h6] h7 h8 h9].
  have h5i := h5 i.
  rewrite ?h0 ?h1 ?h2 ?h4  ?h6 h7 ?h8 ?h9 in *.
  simpl.
  clear h0 h1 h5 h6 h7 h8.
  smt ~no_macros.

- intro *.
  destruct H0 as 
      [[h0 h1 h2] h3 h4 h5 h6 h7 h8 [h9 h10 h11 h12] h13 h14 h15 h16 h17 h18].
  rewrite ?h0 h1 ?h2 ?h3 h4 h5 h6 h7 h8 ?h9  h11 h12 ?h13 h14 h15 h16 h17 h18 in *.
  simpl.
  rewrite forall_true1 in *.
  simpl.
  have h0i0 := h0 i0. 
  have h9i := h9 i.
  have ? := lt_index_total i i0.
  clear h0 h1  h4 h5 h6 h7 h8 h9 h11 h12.
  smt ~no_macros.

- intro *.
  destruct H0 as 
      [[h0 h1 h2 h3] h4 h6 h7 h8 h9 h10 [h11 h12] h13 h14 h15].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4  ?h6 h7 h8 h9 h10 ?h11 ?h12 h13 ?h14 h15 in *.
  simpl.
  clear h0 h1 h2 h6 h7 h8 h9 h11 h14.
  smt ~no_macros.

- intro *.
  destruct H0 as 
  [[h0 h1 h2] h3 h4 h5 h6 h7 h8 h9 
   [h10 h11 h12 h13] h14 h15 h16 h17 h18 h19 h20].  
  rewrite ?h0 h1 ?h2 ?h3  h4 h5 h6 h7 h8 h9 
   ?h10  h12 h13 ?h14 h15 h16 h17 h18 h19 h20 in *.
  simpl.
  rewrite forall_true1 /= in *. 
  have h0i0 := h0 i0 => {h0}.
  have h10i := h10 i => {h10}.
  have ? := lt_index_total i i0.
  clear h1 h4 h5 h6 h7 h8 h9 h12 h13.
  smt ~no_macros.  

- intro *.
  destruct H0 as 
      [[h0 h1 h2 h3] h4 h5 h6 h7 h8 h9 h10 [ h11 h12] h13 h14 h15].
  rewrite ?h0 ?h1 ?h2 ?h3 ?h4 h5 h6 h7 h8 h9 
   ?h10 ?h12 h13 h14 h15 in *. 
  simpl.
  clear h0 h1 h2 h5 h6 h7 h8 h9 h11 h14.
  smt ~no_macros.

- by intro *.
- by intro *.
- intro *.
  clear H0.  
  apply len_zero_enc2_1.
- intro *.
  clear H0.
  apply len_zero_enc2_0.
- intro *.
  destruct H0 as [h0 h1 h2].
  apply h0. 
  apply format_inj[ctxt].  
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h1.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h0.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h1.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h0.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.

- intro *.
  destruct H0 as [h0 h1 h2].
  apply h1.
  apply format_inj[ctxt]. 
  rewrite Meq.
  by project.
- intro *.
  clear H0.  
  apply len_zero_enc2_1.
- intro *.
  clear H0.
  apply len_zero_enc2_0.
- intro *.
  clear H0.  
  apply len_zero_enc2_0.
- intro *.
  clear H0.
  apply len_zero_enc2_1.
Qed.

