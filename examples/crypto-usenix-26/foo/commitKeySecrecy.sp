
(*------------------------------------------------------------------*)
include Core.
include Libs.
include Games.
include[admit] processes.
include WeakSecrecy.
include[admit] blinding.
include[admit] macros.

(*------------------------------------------------------------------*)
namespace CommitKeySecrecy.

(* Starting from the system after the application of `CCA`, replace
   the last phase of the protocol (where the mix-net publishes the
   opening keys of the voters), since we are before the execution of
   the action `MOP`.

   Replacing `MOP` by a dummy action helps Squirrel realize that there
   is no leakage of the mixnet state updates in `MOC _` through the
   publication of this update in `MOP`. A finer-grained analysis of
   the origins of macros's bodies during the derecursivation. would
   allow to avoid this simple system hop. *)
system P =
  let vA  = diff(v0,v1) in
  let vB  = diff(v1,v0) in 
  let kcA = diff(kc0,kc1) in
  let kcB = diff(kc1,kc0) in
  let cmA = comm vA kcA in
  let cmB = comm vB kcB in
  Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
  ( (A   : Alice_CCA              (cmA,kcA,pkAdmin)          )
  | (B   : Bob_CCA                (cmB,kcB,pkAdmin)          )
  | (MVC : mixer_vote_collect_CCA (cmA,cmB,pkAdmin)          )
  | (MVP : mixer_vote_publish                                )
  | (BBS : set_BB                                            )
  | (MOC : mixer_open_collect_CCA (cmA,cmB,kcA,kcB,pkAdmin)  )
  | (MOP : Dummy.mixer_open_publish                          )
).

(*------------------------------------------------------------------*)
(* auxiliary lemma, replaying the proof of `box_nan` in `macros.sp`
   for the system `P` instead of `Privacy_CCA` *)
lemma [P] box_nan (t:timestamp) (i:index):
  not (happens(MVC i)) => happens t => box(i)@t = zero.
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

(*------------------------------------------------------------------*)
namespace Left.
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

  (* auxiliary lemma *)
  lemma [Privacy_CCA/left,P/left] bb_val (t:_): 
    BBS <= t => BB@t = read (input@BBS).
  Proof.
    induction t.
    intro t IH T. 
    case t => H.
    + auto.
    + by depends Start, BBS. 
    + by have ? // := Trace.Aauth_BBS.
    + by have ? // := Trace.Avote_BBS.
    + rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.BBS_Aopening _. 
    + by have ? // := Trace.Bauth_BBS.
    + by have ? // := Trace.Bvote_BBS.
    + rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.BBS_Bopening _. 
    + destruct H as [i H].
      by have ? // := Trace.MVC_BBS i.
    + rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.BBS_MVP. 
    + rewrite /BB /bb. 
      auto ~diffr. 
    + destruct H as [j H]. 
      rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.BBS_MOC j. 
    + rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.any_MOP BBS. 
  Qed.

  (* auxiliary lemma *)
  lemma [Privacy_CCA/left,P/left] box_val (i,t:_): 
    MVC i <= t => box i@t = box i@MVC i.
  Proof.
    set b := box i @MVC i.
    induction t.
    intro t IH T. 
    case t => H; try (rewrite /box; by apply IH).
    + auto.
    + destruct H as [_ H]. 
      case i = i0; 1: intro U; rewrite H /b U; apply eq_refl. 
      intro U.
      rewrite /box if_false; 1:auto.
      by apply IH.
    + destruct H as [_ H]. 
      rewrite /box; by apply IH.
  Qed.

  (* Bridging step, preparing the way for the reduction to Commit Key Secrecy. *)
  global lemma switch
    @system:(Privacy_CCA/left,P/left)
    (t:_[const])
  :  
    [happens(BBS)] ->
    [t < MOP] ->
    equiv(
      frame@t, 
      tkA, tkB,  kc0, kc1, v0, v1,
      seedA_enc2,
      seedB_enc2,
      sk_mix2,
      sk_mix1,
      seedA_enc1,
      seedB_enc1,
      rdAdmin).
  Proof. 
    intro Hap Bound.
    have HapStart : happens Start by depends Start, MOP.

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
      rewrite /frame /output exec_val /* //=. 
      simpl ~diffr. 
      fa !<_,_>, if _ then _ else _, _ && _.
      have ? : Avote < t by have ? := Trace.Avote_Aopening.
      have ? : BBS < t by have ? := Trace.BBS_Aopening _.
      rewrite bb_val //. 
      by apply IH (pred t).
  
    (* Bopening *)
    - intro H. 
      rewrite /frame /output exec_val /* //=. 
      simpl ~diffr. 
      fa !<_,_>, if _ then _ else _, _ && _.
      have ? : Bvote < t by have ? := Trace.Bvote_Bopening.
      have ? : BBS < t by have ? := Trace.BBS_Bopening _.
      rewrite bb_val //. 
      by apply IH (pred t).
  
    (* MVP *)
    - intro H. 
      rewrite /frame /output exec_val /* //=. 
      simpl ~diffr. 
      fa !<_,_>, if _ then _ else _.
      rewrite box_val; 1: intro i j *; by have ? := Trace.MVC_MVP j _.
      rewrite (box_val _ (pred MVP)); 1: intro i j *; by have ? := Trace.MVC_MVP i _.

      have ? := Trace.happens_Avote.
      have ? := Trace.happens_Bvote.

      (* deal with the `shuffle` *) 
      ghave E : [
         forall i, 
           box i@pred MVP = 
           if happens (MVC i) && 
              MVC i < MVP &&             (* this is to tell bideduction later (in `apply IH ...`) *)
              Avote < MVP && Bvote < MVP (* idem *)
           then box i@MVC i 
           else zero
      ]. {
        intro i.
        rewrite Trace.MVC_MVP /=; 1:auto.
        rewrite Trace.Avote_MVP /=; 1:auto.
        rewrite Trace.Bvote_MVP /=; 1:auto.
        case happens (MVC i) => HapMVC /=. 
        + apply box_val. 
          by have ? // := Trace.MVC_MVP i _.
        + project; [1: by rewrite Macro.box_nan | 2: by rewrite box_nan].
         (* twice the same lemma, but for the two different system involved. *)
      }.
      rewrite E in 2 => {E}.

      (* deal with the `forall` *)
      ghave E :
      [
        (forall (i,j:index),
         happens(MVC(i), MVC(j)) => box i@MVC(i) = box j@MVC(j) => i = j) 
        =
        (forall (i,j:index),
           happens(MVC(i), MVC(j)) => 
           MVC i < MVP => MVC j < MVP => (* this is to tell bideduction later (in `apply IH ...`) *)
           Avote < MVP => Bvote < MVP => (* idem *)
           box i@MVC(i) = box j@MVC(j) => i = j) 
       ]. {
         rewrite !Trace.MVC_MVP // !Trace.Avote_MVP // !Trace.Bvote_MVP //=.
      }.
      rewrite E => {E}.

      (* conclude the proof by deduction and the induction hypothesis *)
      rewrite /* in 1,2.
      (* `1` is `forall (i,j:index), happens(MVC(i),MVC(j)) => ...` 
         `2` is `shuffle (fun (i:index) => if happens(MVC(i)) then box i@MVC(i))` *)
      simpl ~diffr.
      by apply IH (pred t).

    (* MOP *)
    - intro H. 
      constraints.
  Qed.

  (* secrecy of the commit key `kc0` in the protocol `Pricacy_CCA/left` *)
  lemma kc0_secrecy
    @set:(Privacy_CCA/left) 
    @equiv:(P/left,P/left) 
    (j:_[const,glob]) 
  :
    happens(MOP, MOC(j),BBS) =>
    kc0 = read (snd (decr (read (input@MOC(j))) sk_mix2)) =>
    false.
  Proof.
    intro Hap M. 
    rewrite equiv switch (MOC j); [1: auto | 2: by apply Trace.any_MOP].
    ghave E :
      equiv( 
        diff(kc0 = read (snd (decr (read (input@MOC(j))) sk_mix2)),
             false)
      ). {
      crypto CommitmentKeyHiding 
        (key:kc0)
        (commited_message: v0); 
      try auto.
    }.
    by rewrite equiv E.
  Qed.

  (* secrecy of the commit key `kc1` in the protocol `Pricacy_CCA/left` *)
  lemma kc1_secrecy
    @set:(Privacy_CCA/left) 
    @equiv:(P/left,P/left) 
    (j:_[const,glob]) 
  :
    happens(MOP, MOC(j),BBS) =>
    kc1 = read (snd (decr (read (input@MOC(j))) sk_mix2)) =>
    false.
  Proof.
    intro Hap M. 
    rewrite equiv switch (MOC j); [1: auto | 2: by apply Trace.any_MOP].
    ghave E :
      equiv( 
        diff(kc1 = read (snd (decr (read (input@MOC(j))) sk_mix2)),
             false)
      ). {
      crypto CommitmentKeyHiding 
        (key:kc1)
        (commited_message: v1); 
      try auto.
    }.
    by rewrite equiv E.
  Qed.
end Left.

(* Similar proof, but for the right system [Privacy_CCA/right].

   All lemmas are exactly identical but for the last lemma
   `commit_key_hiding`, which has only minor changes (replace `kc0`
   and `v0` by their counter-parts in the right system, which are
   respectively `kc1` and `v1`). *)
(*------------------------------------------------------------------*)
namespace Right.
  (* auxiliary lemma *)
  lemma [Privacy_CCA/right,P/right] exec_val (t:_): 
    happens(t) => exec@t = true.
  Proof.
    induction t.
    intro *.
    case t;  try( intro Eq; rewrite /exec; by rewrite H).
    * auto.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
    * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
  Qed.

  (* auxiliary lemma *)
  lemma [Privacy_CCA/right,P/right] bb_val (t:_): 
    BBS <= t => BB@t = read (input@BBS).
  Proof.
    induction t.
    intro t IH T. 
    case t => H.
    + auto.
    + by depends Start, BBS. 
    + by have ? // := Trace.Aauth_BBS.
    + by have ? // := Trace.Avote_BBS.
    + rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.BBS_Aopening _. 
    + by have ? // := Trace.Bauth_BBS.
    + by have ? // := Trace.Bvote_BBS.
    + rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.BBS_Bopening _. 
    + destruct H as [i H].
      by have ? // := Trace.MVC_BBS i.
    + rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.BBS_MVP. 
    + rewrite /BB /bb. 
      auto ~diffr. 
    + destruct H as [j H]. 
      rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.BBS_MOC j. 
    + rewrite /BB. 
      apply IH; 1: auto.
      have ? // := Trace.any_MOP BBS. 
  Qed.

  (* auxiliary lemma *)
  lemma [Privacy_CCA/right,P/right] box_val (i,t:_): 
    MVC i <= t => box i@t = box i@MVC i.
  Proof.
    set b := box i @MVC i.
    induction t.
    intro t IH T. 
    case t => H; try (rewrite /box; by apply IH).
    + auto.
    + destruct H as [_ H]. 
      case i = i0; 1: intro U; rewrite H /b U; apply eq_refl. 
      intro U.
      rewrite /box if_false; 1:auto.
      by apply IH.
    + destruct H as [_ H]. 
      rewrite /box; by apply IH.
  Qed.

  global lemma switch
    @system:(Privacy_CCA/right,P/right)
    (t:_[const])
  :  
    [happens(BBS)] ->
    [t < MOP] ->
    equiv(
      frame@t, 
      tkA, tkB,  kc0, kc1, v0, v1,
      seedA_enc2,
      seedB_enc2,
      sk_mix2,
      sk_mix1,
      seedA_enc1,
      seedB_enc1,
      rdAdmin).
  Proof. 
    intro Hap Bound.
    have HapStart : happens Start by depends Start, MOP.

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
      rewrite /frame /output exec_val /* //=. 
      simpl ~diffr. 
      fa !<_,_>, if _ then _ else _, _ && _.
      have ? : Avote < t by have ? := Trace.Avote_Aopening.
      have ? : BBS < t by have ? := Trace.BBS_Aopening _.
      rewrite bb_val //. 
      by apply IH (pred t).
  
    (* Bopening *)
    - intro H. 
      rewrite /frame /output exec_val /* //=. 
      simpl ~diffr. 
      fa !<_,_>, if _ then _ else _, _ && _.
      have ? : Bvote < t by have ? := Trace.Bvote_Bopening.
      have ? : BBS < t by have ? := Trace.BBS_Bopening _.
      rewrite bb_val //. 
      by apply IH (pred t).
  
    (* MVP *)
    - intro H. 
      rewrite /frame /output exec_val /* //=. 
      simpl ~diffr. 
      fa !<_,_>, if _ then _ else _.
      rewrite box_val; 1: intro i j *; by have ? := Trace.MVC_MVP j _.
      rewrite (box_val _ (pred MVP)); 1: intro i j *; by have ? := Trace.MVC_MVP i _.

      have ? := Trace.happens_Avote.
      have ? := Trace.happens_Bvote.

      (* deal with the `shuffle` *) 
      ghave E : [
         forall i, 
           box i@pred MVP = 
           if happens (MVC i) && 
              MVC i < MVP &&             (* this is to tell bideduction later (in `apply IH ...`) *)
              Avote < MVP && Bvote < MVP (* idem *)
           then box i@MVC i 
           else zero
      ]. {
        intro i.
        rewrite Trace.MVC_MVP /=; 1:auto.
        rewrite Trace.Avote_MVP /=; 1:auto.
        rewrite Trace.Bvote_MVP /=; 1:auto.
        case happens (MVC i) => HapMVC /=. 
        + apply box_val. 
          by have ? // := Trace.MVC_MVP i _.
        + project; [1: by rewrite Macro.box_nan | 2: by rewrite box_nan].
         (* twice the same lemma, but for the two different system involved. *)
      }.
      rewrite E in 2 => {E}.

      (* deal with the `forall` *)
      ghave E :
      [
        (forall (i,j:index),
         happens(MVC(i), MVC(j)) => box i@MVC(i) = box j@MVC(j) => i = j) 
        =
        (forall (i,j:index),
           happens(MVC(i), MVC(j)) => 
           MVC i < MVP => MVC j < MVP => (* this is to tell bideduction later (in `apply IH ...`) *)
           Avote < MVP => Bvote < MVP => (* idem *)
           box i@MVC(i) = box j@MVC(j) => i = j) 
       ]. {
         rewrite !Trace.MVC_MVP // !Trace.Avote_MVP // !Trace.Bvote_MVP //=.
      }.
      rewrite E => {E}.

      (* conclude the proof by deduction and the induction hypothesis *)
      rewrite /* in 1,2.
      (* `1` is `forall (i,j:index), happens(MVC(i),MVC(j)) => ...` 
         `2` is `shuffle (fun (i:index) => if happens(MVC(i)) then box i@MVC(i))` *)
      simpl ~diffr.
      by apply IH (pred t).

    (* MOP *)
    - intro H. 
      constraints.
 Qed.

  (* secrecy of the commit key `kc1` in the protocol `Pricacy_CCA/right` *)
  lemma kc1_secrecy
    @set:(Privacy_CCA/right) 
    @equiv:(P/right,P/right) 
    (j:_[const,glob]) 
  :
    happens(MOP, MOC(j),BBS) =>
    kc1 = read (snd (decr (read (input@MOC(j))) sk_mix2)) =>
    false.
  Proof.
    intro Hap M. 
    rewrite equiv switch (MOC j); [1: auto | 2: by apply Trace.any_MOP].
    ghave E :
      equiv( 
        diff(kc1 = read (snd (decr (read (input@MOC(j))) sk_mix2)),
             false)
      ). {
      crypto CommitmentKeyHiding 
        (key:kc1)
        (commited_message: v1); 
      try auto.
    }.
    by rewrite equiv E.
  Qed.

  (* secrecy of the commit key `kc0` in the protocol `Pricacy_CCA/right` *)
  lemma kc0_secrecy
    @set:(Privacy_CCA/right) 
    @equiv:(P/right,P/right) 
    (j:_[const,glob]) 
  :
    happens(MOP, MOC(j),BBS) =>
    kc0 = read (snd (decr (read (input@MOC(j))) sk_mix2)) =>
    false.
  Proof.
    intro Hap M. 
    rewrite equiv switch (MOC j); [1: auto | 2: by apply Trace.any_MOP].
    ghave E :
      equiv( 
        diff(kc0 = read (snd (decr (read (input@MOC(j))) sk_mix2)),
             false)
      ). {
      crypto CommitmentKeyHiding 
        (key:kc0)
        (commited_message: v0); 
      try auto.
    }.
    by rewrite equiv E.
  Qed.
end Right.

(*------------------------------------------------------------------*)
(* Final lemma: secrecy of the `kcA` commit key before the
   last phase of the FOO protocol. *)
lemma kcA_secrecy @set:Privacy_CCA (j :_[const]) :
  let kcA = diff(kc0,kc1) in
  happens(MOP, MOC(j),BBS) =>
  kcA = read (snd (decr (read (input@MOC(j))) sk_mix2)) =>
  false.
Proof.
  project. 
  (* FIXME: generalizing allows to obtain the `glob` tag *)
  + generalize dependent j => j *.
    by apply CommitKeySecrecy.Left.kc0_secrecy j.
  (* FIXME: generalizing allows to obtain the `glob` tag *)
  + generalize dependent j => j *.
    by apply CommitKeySecrecy.Right.kc1_secrecy j.
Qed.

(* Final lemma: secrecy of the `kcB` commit key before the
   last phase of the FOO protocol. *)
lemma kcB_secrecy @set:Privacy_CCA (j :_[const]) :
  let kcB = diff(kc1,kc0) in
  happens(MOP, MOC(j),BBS) =>
  kcB = read (snd (decr (read (input@MOC(j))) sk_mix2)) =>
  false.
Proof.
  project. 
  (* FIXME: generalizing allows to obtain the `glob` tag *)
  + generalize dependent j => j *.
    by apply CommitKeySecrecy.Left.kc1_secrecy j.
  (* FIXME: generalizing allows to obtain the `glob` tag *)
  + generalize dependent j => j *.
    by apply CommitKeySecrecy.Right.kc0_secrecy j.
Qed.
end CommitKeySecrecy.
