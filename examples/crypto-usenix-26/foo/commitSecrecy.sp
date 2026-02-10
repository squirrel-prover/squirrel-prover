(* In this file, we show a secrecy property of Alice and Bob's commit
   to their vote, which are respectively `cmA` and `cmB`, in the first
   phase of the protocol (more precisely before the first mixnet
   publishes its data, which corresponds to the action `MVP` in our
   modeling).

   The proof are almost identical, so we focus the high-level
   description on the proof of secrecy of Alice's commit `cmA`, which
   culminate in the lemma `CommitSecrecy.Alice.secrecy`, which
   (roughly) state that:

     `cmA <> adversary computation @ t`   (where `t < MVP`)

   Its proof is structured as follow:

   - Starts from the `Privacy_CCA` protocol, which is the FOO protocol
     after the idealization of the encryptions to the mixnets.

   - The proof consists in two similar sub-proofs: one reasoning on
     the left protocol `Privacy_CCA/left`, the other on the right
     protocol `Privacy_CCA/right`. We focus on the former, which is
     developped in the namespace `Alice.Left`.

   - First, lemma `Alice.Left.switch` is a lossless bridging step
     switching protocol to `Alice.Left.P`, to prepare the way for the
     next step.

   - Second, lemma `Alice.Left.equiv_by_blinding` applies the Blinding
     property of the blind signature to replace the blinding of `cmA`
     by a blinding of `zero`.

   - Finally, lemma `Alice.Left.secrecy` observes that at that point,
     `cmA` no longer transit over the network, and we can replace the
     commited value by a random and fresh value using the Commitment
     Hiding property. We conclude by a trivial freshness argument.
*)

(*------------------------------------------------------------------*)
include Core.
include Libs.
include Games.
include[admit] processes.
include WeakSecrecy.
include[admit] blinding.

(*------------------------------------------------------------------*)
namespace CommitSecrecy.

(* dummy blinding signature used during the reduction to Blinding *)
name dummy : token_bsign.

(* fresh random value used to obtain secrecy at the end of the proof
   (e.g. in the `Alice.Left.secrecy` lemma) *)
name nfresh : message.

(*------------------------------------------------------------------*)
(* Starting from the system after the application of `CCA`, replace 
   the commitment `cmA` in Alice's output by `0`. 

   Further, we replace the later-phases processes by dummy processes,
   since we will only reason on the this system in the first phase. *)
namespace Alice.Left.
  system P =
    let vA  = v0 in
    let vB  = v1 in
    let kcA = kc0 in
    let kcB = kc1 in
    let cmA = comm vA kcA in
    let cmB = comm vB kcB in
    Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
    ( (A   : Alice_CCA (diff(cmA,zero),kcA,pkAdmin)            )
    | (B   : Bob_CCA   (cmB           ,kcB,pkAdmin)            )
    | (MVC : mixer_vote_collect_CCA(cmA,cmB,pkAdmin)           )
    | (MVP : Dummy.mixer_vote_publish                          )
    | (BBS : set_BB                                            )
    | (MOC : Dummy.mixer_open_collect                          )
    | (MOP : Dummy.mixer_open_publish                          )
 ).

  (* auxiliary lemma *)
  lemma [Privacy_CCA/left,P/left] exec_val (t:_): 
    happens(t) => exec@t = true.
  Proof.
    induction t.
    intro *.
    case t;  try( intro Eq; rewrite /exec; by rewrite H).
    * auto.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
  Qed.

  (* Bridging step, preparing the way for the reduction to Blinding. *)
  global lemma switch
    @system:(Privacy_CCA/left,P/left)
    (t:_[const])
  :
    [t < MVP] ->
    Let vA  = v0 in
    Let kcA = kc0 in
    Let cmA = comm vA kcA in
    equiv(
      cmA, frame@t, input@t,
      tkA, tkB,  kc0, kc1, v0, v1,
      seedA_enc2,
      seedB_enc2,
      sk_mix2,
      sk_mix1,
      seedA_enc1,
      seedB_enc1,
      rdAdmin).
  Proof. 
    intro Bound *.
    have HapStart : happens Start by depends Start, MVP.

    revert Bound.  
    generalize t as t. 

    induction => t IH Bound.
    case t;
    try (
      intro H;
      try destruct H;
      rewrite /frame /output exec_val /* //; 
      by apply IH (pred t)
    ).

    (* init *)
    - by intro ?.

    (* Aopening *)
    - intro H. 
      have ? := Trace.Aopening_MVP. 
      constraints.
  
    (* Bopening *)
    - intro H. 
      have ? := Trace.Bopening_MVP. 
      constraints.
  
    (* MVP *)
    - intro H.
      constraints.
  
    (* MOP *)
    - intro H.
      have ? // := Trace.any_MOP MVP _ _. 
      constraints.
  Qed.

  (* Application of the Blinding property of blind signatures. *)
  global lemma equiv_by_blinding @system:P (t:_[const]) :
    [t < MVP] ->
    Let vA  = v0 in
    Let kcA = kc0 in
    Let cmA = comm vA kcA in
    equiv(cmA, input@t, sk_mix1).
  Proof. 
    intro H *. 
    (* We are going to use the adaptative selective failure blindness
       assumption to replace the message `cmA` blinded by Alice's by
       `zero`.
    
       - As we are in the first phase of the protocol, we only use the
         `blind` and `baccept` functions of the blinding scheme. Thus,
         we do not need the more complexe unblinding oracle, which
         simplifies the arguments.
    
       - Further, we only swap a single blinded value, taking `token0`
         to be `tkA`). As the other token `token1` is not needed, we set
         it to a dummy name, to prevent `crypto` from using it.  *)
    crypto AdaptativeSelectiveFailureBlindness
      (m0 : Left.cmA@Start)
      (m1 : zero)
      (pk : pkAdmin)
      (token0 : tkA)
      (token1 : dummy);
    try auto.
    + intro [? A].
       by have ? := Trace.Aopening_MVP.
    + right. 
      by have ? := Trace.Aopening_MVP.
  Qed.
  
  (* Application of Commitment Hiding + some basic freshness reasoning. *)
  lemma secrecy @set:(P/right) @equiv:(P/right,P/right) (t:_[const]) :
    let vA  = v0 in
    let kcA = kc0 in
    let cmA = comm vA kcA in
    t < MVP =>
    cmA <> fst (decr (read (input@t)) sk_mix1).
  Proof. 
    intro vA kcA cmA Hap Eq.
    rewrite /cmA /kcA /vA in *; clear.
    ghave E :
      equiv(comm diff(v0,nfresh) kc0, input@t, sk_mix1). {
      crypto CommitmentHiding.
    }.
    rewrite equiv E.
    clear E.
    apply f_apply (fun x => copen x kc0) in Eq => /=.
    rewrite copen_comm in Eq.
    fresh Eq. 
  Qed.
end Alice.Left.


(*------------------------------------------------------------------*)
namespace Alice.Right.

  system P =
    let vA  = v1 in
    let vB  = v0 in
    let kcA = kc1 in
    let kcB = kc0 in
    let cmA = comm vA kcA in
    let cmB = comm vB kcB in
    Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
    ( (A   : Alice_CCA (diff(cmA,zero),kcA,pkAdmin)            )
    | (B   : Bob_CCA   (cmB           ,kcB,pkAdmin)            )
    | (MVC : mixer_vote_collect_CCA(cmA,cmB,pkAdmin)           )
    | (MVP : Dummy.mixer_vote_publish                          )
    | (BBS : set_BB                                            )
    | (MOC : Dummy.mixer_open_collect                          )
    | (MOP : Dummy.mixer_open_publish                          )
  ).

  (* auxiliary lemma *)  
  lemma [Privacy_CCA/right,P/left] exec_val (t:_): 
    happens(t) => exec@t = true.
  Proof.
    induction t.
    intro *.
    case t;  try( intro Eq; rewrite /exec; by rewrite H).
    * auto.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
  Qed.

  (* Bridging step, preparing the way for the reduction to Blinding. *)
  global lemma switch
    @system:(Privacy_CCA/right,P/left)
    (t:_[const])
  :
    [t < MVP] ->
    Let vA  = v1 in
    Let kcA = kc1 in
    Let cmA = comm vA kcA in
    equiv(
      cmA, frame@t, 
      tkA, tkB,  kc0, kc1, v0, v1,
      seedA_enc2,
      seedB_enc2,
      sk_mix2,
      sk_mix1,
      seedA_enc1,
      seedB_enc1,
      rdAdmin).
  Proof. 
    intro Bound *.
    have HapStart : happens Start by depends Start, MVP.

    revert Bound.  
    generalize t as t. 

    induction => t IH Bound.
    case t;
    try (
      intro H;
      try destruct H;
      rewrite /frame /output exec_val /* //; 
      by apply IH (pred t)
    ).

    (* init *)
    - by intro ?.

    (* Aopening *)
    - intro H. 
      have ? := Trace.Aopening_MVP. 
      constraints.
  
    (* Bopening *)
    - intro H. 
      have ? := Trace.Bopening_MVP. 
      constraints.
  
    (* MVP *)
    - intro H.
      constraints.
  
    (* MOP *)
    - intro H.
      have ? // := Trace.any_MOP MVP _ _. 
      constraints.
  Qed.

  (* Application of the Blinding property of blind signatures. *)  
  global lemma equiv_by_blinding @system:P (t:_[const]) :
    [t < MVP] ->
    Let vA  = v1 in
    Let kcA = kc1 in
    Let cmA = comm vA kcA in
    equiv(cmA, input@t, sk_mix1).
  Proof. 
    intro H *. 
    (* See `Alice.Left.equiv_by_blinding` for a explanation *)
    crypto AdaptativeSelectiveFailureBlindness
      (m0 : Right.cmA@Start)
      (m1 : zero)
      (pk : pkAdmin)
      (token0 : tkA)
      (token1 : dummy);
    try auto.
    + intro [? A].
       by have ? := Trace.Aopening_MVP.
    + right. 
      by have ? := Trace.Aopening_MVP.
  Qed.

  (* Application of Commitment Hiding + some basic freshness reasoning. *)
  lemma secrecy @set:(P/right) @equiv:(P/right,P/right) (t:_[const]) :
    let vA  = v1 in
    let kcA = kc1 in
    let cmA = comm vA kcA in
    t < MVP =>
    cmA <> fst (decr (read (input@t)) sk_mix1).
  Proof. 
    intro vA kcA cmA Hap Eq.
    rewrite /cmA /kcA /vA in *; clear.
    ghave E :
      equiv(comm diff(v1,nfresh) kc1, input@t, sk_mix1). {
      crypto CommitmentHiding.
    }.
    rewrite equiv E.
    clear E.
    apply f_apply (fun x => copen x kc1) in Eq => /=.
    rewrite copen_comm in Eq.
    fresh Eq. 
  Qed.
end Alice.Right.

(*------------------------------------------------------------------*)
namespace Alice.
(* Final lemma: secrecy of Alice's in phase 1 of the FOO protocol. *)
lemma secrecy @set:Privacy_CCA (t :_[const]) :
  t < MVP =>
  Top.cmA@Start <> fst (decr (read (input@t)) sk_mix1).
Proof.
  project.
  (* FIXME: generalizing over `t` allows to obtain the `glob` tag *)
  + generalize t => t. 
    intro H. 
    (* FIXME: this should not be necessary, it seems `rewrite equiv`
       does not rely enough on reduction *)
    rewrite /cmA /kcA /vA /v0. 
    rewrite equiv Alice.Left.switch t; 1: constraints.
    rewrite equiv Alice.Left.equiv_by_blinding t; 1:auto.
    by apply Alice.Left.secrecy.
  (* FIXME: generalizing over `t` allows to obtain the `glob` tag *)
  + generalize t => t. 
    intro H. 
    (* FIXME: same remark as above *)
    rewrite /cmA /kcA /vA /v1. 
    rewrite equiv Alice.Right.switch t; 1:constraints.
    rewrite equiv Alice.Right.equiv_by_blinding t; 1:auto.
    by apply Alice.Right.secrecy.
Qed.
end Alice.


(*==================================================================*)
(* Similar proof to `Alice.Left` and `Alice.Right`, but for `Bob`. *)
namespace Bob.Left.
  system P =
    let vA  = v0 in
    let vB  = v1 in
    let kcA = kc0 in
    let kcB = kc1 in
    let cmA = comm vA kcA in
    let cmB = comm vB kcB in
    Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
    ( (A   : Alice_CCA (cmA           ,kcA,pkAdmin)            )
    | (B   : Bob_CCA   (diff(cmB,zero),kcB,pkAdmin)            )
    | (MVC : mixer_vote_collect_CCA(cmA,cmB,pkAdmin)           )
    | (MVP : Dummy.mixer_vote_publish                          )
    | (BBS : set_BB                                            )
    | (MOC : Dummy.mixer_open_collect                          )
    | (MOP : Dummy.mixer_open_publish                          )
 ).

  (* auxiliary lemma *)
  lemma [Privacy_CCA/left,P/left] exec_val (t:_): 
    happens(t) => exec@t = true.
  Proof.
    induction t.
    intro *.
    case t;  try( intro Eq; rewrite /exec; by rewrite H).
    * auto.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
  Qed.

  (* Bridging step, preparing the way for the reduction to Blinding. *)
  global lemma switch
    @system:(Privacy_CCA/left,P/left)
    (t:_[const])
  :
    [t < MVP] ->
    Let vB  = v1 in
    Let kcB = kc1 in
    Let cmB = comm vB kcB in
    equiv(
      cmB, frame@t, input@t,
      tkA, tkB,  kc0, kc1, v0, v1,
      seedA_enc2,
      seedB_enc2,
      sk_mix2,
      sk_mix1,
      seedA_enc1,
      seedB_enc1,
      rdAdmin).
  Proof. 
    intro Bound *.
    have HapStart : happens Start by depends Start, MVP.

    revert Bound.  
    generalize t as t. 

    induction => t IH Bound.
    case t;
    try (
      intro H;
      try destruct H;
      rewrite /frame /output exec_val /* //; 
      by apply IH (pred t)
    ).

    (* init *)
    - by intro ?.

    (* Aopening *)
    - intro H. 
      have ? := Trace.Aopening_MVP. 
      constraints.
  
    (* Bopening *)
    - intro H. 
      have ? := Trace.Bopening_MVP. 
      constraints.
  
    (* MVP *)
    - intro H.
      constraints.
  
    (* MOP *)
    - intro H.
      have ? // := Trace.any_MOP MVP _ _. 
      constraints.
  Qed.

  (* Application of the Blinding property of blind signatures. *)
  global lemma equiv_by_blinding @system:P (t:_[const]) :
    [t < MVP] ->
    Let vB  = v1 in
    Let kcB = kc1 in
    Let cmB = comm vB kcB in
    equiv(cmB, input@t, sk_mix1).
  Proof. 
    intro H *. 
    crypto AdaptativeSelectiveFailureBlindness
      (m0 : Left.cmB@Start)
      (m1 : zero)
      (pk : pkAdmin)
      (token0 : tkB)
      (token1 : dummy);
    try auto.
    + intro [? A].
       by have ? := Trace.Bopening_MVP.
    + right. 
      by have ? := Trace.Bopening_MVP.
  Qed.
  
  (* Application of Commitment Hiding + some basic freshness reasoning. *)
  lemma secrecy @set:(P/right) @equiv:(P/right,P/right) (t:_[const]) :
    let vB  = v1 in
    let kcB = kc1 in
    let cmB = comm vB kcB in
    t < MVP =>
    cmB <> fst (decr (read (input@t)) sk_mix1).
  Proof. 
    intro vB kcB cmB Hap Eq.
    rewrite /cmB /kcB /vB in *; clear.
    ghave E :
      equiv(comm diff(v1,nfresh) kc1, input@t, sk_mix1). {
      crypto CommitmentHiding.
    }.
    rewrite equiv E.
    clear E.
    apply f_apply (fun x => copen x kc1) in Eq => /=.
    rewrite copen_comm in Eq.
    fresh Eq. 
  Qed.
end Bob.Left.


(*------------------------------------------------------------------*)
namespace Bob.Right.

  system P =
    let vA  = v1 in
    let vB  = v0 in
    let kcA = kc1 in
    let kcB = kc0 in
    let cmA = comm vA kcA in
    let cmB = comm vB kcB in
    Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
    ( (A   : Alice_CCA (cmA           ,kcA,pkAdmin)            )
    | (B   : Bob_CCA   (diff(cmB,zero),kcB,pkAdmin)            )
    | (MVC : mixer_vote_collect_CCA(cmA,cmB,pkAdmin)           )
    | (MVP : Dummy.mixer_vote_publish                          )
    | (BBS : set_BB                                            )
    | (MOC : Dummy.mixer_open_collect                          )
    | (MOP : Dummy.mixer_open_publish                          )
  ).

  (* auxiliary lemma *)  
  lemma [Privacy_CCA/right,P/left] exec_val (t:_): 
    happens(t) => exec@t = true.
  Proof.
    induction t.
    intro *.
    case t;  try( intro Eq; rewrite /exec; by rewrite H).
    * auto.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
  Qed.

  (* Bridging step, preparing the way for the reduction to Blinding. *)
  global lemma switch
    @system:(Privacy_CCA/right,P/left)
    (t:_[const])
  :
    [t < MVP] ->
    Let vA  = v1 in
    Let kcA = kc1 in
    Let cmA = comm vA kcA in
    equiv(
      cmA, frame@t, 
      tkA, tkB,  kc0, kc1, v0, v1,
      seedA_enc2,
      seedB_enc2,
      sk_mix2,
      sk_mix1,
      seedA_enc1,
      seedB_enc1,
      rdAdmin).
  Proof. 
    intro Bound *.
    have HapStart : happens Start by depends Start, MVP.

    revert Bound.  
    generalize t as t. 

    induction => t IH Bound.
    case t;
    try (
      intro H;
      try destruct H;
      rewrite /frame /output exec_val /* //; 
      by apply IH (pred t)
    ).

    (* init *)
    - by intro ?.

    (* Aopening *)
    - intro H. 
      have ? := Trace.Aopening_MVP. 
      constraints.
  
    (* Bopening *)
    - intro H. 
      have ? := Trace.Bopening_MVP. 
      constraints.
  
    (* MVP *)
    - intro H.
      constraints.
  
    (* MOP *)
    - intro H.
      have ? // := Trace.any_MOP MVP _ _. 
      constraints.
  Qed.

  (* Application of the Blinding property of blind signatures. *)  
  global lemma equiv_by_blinding @system:P (t:_[const]) :
    [t < MVP] ->
    Let vB  = v0 in
    Let kcB = kc0 in
    Let cmB = comm vB kcB in
    equiv(cmB, input@t, sk_mix1).
  Proof. 
    intro H *. 
    crypto AdaptativeSelectiveFailureBlindness
      (m0 : Right.cmB@Start)
      (m1 : zero)
      (pk : pkAdmin)
      (token0 : tkB)
      (token1 : dummy);
    try auto.
    + intro [? A].
       by have ? := Trace.Bopening_MVP.
    + right. 
      by have ? := Trace.Bopening_MVP.
  Qed.

  (* Application of Commitment Hiding + some basic freshness reasoning. *)
  lemma secrecy @set:(P/right) @equiv:(P/right,P/right) (t:_[const]) :
    let vB  = v0 in
    let kcB = kc0 in
    let cmB = comm vB kcB in
    t < MVP =>
    cmB <> fst (decr (read (input@t)) sk_mix1).
  Proof. 
    intro vB kcB cmB Hap Eq.
    rewrite /cmB /kcB /vB in *; clear.
    ghave E :
      equiv(comm diff(v0,nfresh) kc0, input@t, sk_mix1). {
      crypto CommitmentHiding.
    }.
    rewrite equiv E.
    clear E.
    apply f_apply (fun x => copen x kc0) in Eq => /=.
    rewrite copen_comm in Eq.
    fresh Eq. 
  Qed.
end Bob.Right.

(*------------------------------------------------------------------*)
namespace Bob.
(* Final lemma: secrecy of Bob's in phase 1 of the FOO protocol. *)
lemma secrecy @set:Privacy_CCA (t :_[const]) :
  t < MVP =>
  Top.cmB@Start <> fst (decr (read (input@t)) sk_mix1).
Proof.
  project.
  (* FIXME: generalizing over `t` allows to obtain the `glob` tag *)
  + generalize t => t. 
    intro H. 
    (* FIXME: this should not be necessary, it seems `rewrite equiv`
       does not rely enough on reduction *)
    rewrite /cmB /kcB /vB /v1. 
    rewrite equiv Bob.Left.switch t; 1: constraints.
    rewrite equiv Bob.Left.equiv_by_blinding t; 1:auto.
    by apply Bob.Left.secrecy.
  (* FIXME: generalizing over `t` allows to obtain the `glob` tag *)
  + generalize t => t. 
    intro H. 
    (* FIXME: same remark as above *)
    rewrite /cmB /kcB /vB /v0. 
    rewrite equiv Bob.Right.switch t; 1:constraints.
    rewrite equiv Bob.Right.equiv_by_blinding t; 1:auto.
    by apply Bob.Right.secrecy.
Qed.
end Bob.
end CommitSecrecy.
