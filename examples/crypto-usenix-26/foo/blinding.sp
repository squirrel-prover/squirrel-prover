(*************************
#  Blinding property
**************************)

include[admit] Core.
include[admit] NonDeduction.
include[admit] Libs.
include[admit] Games.
include[admit] processes.

(* set verboseCrypto  = true. *)
(* set logUnsatCrypto = "unsat.txt". *)
(* set logMemCrypto   = "mem.txt". *)

(*------------------------------------------------------------------*)
(* Dummy processes to defined the `Blinding` system below. *)
namespace Dummy.
  process mixer_vote_publish = out(c, empty).
   
  process mixer_open_collect =
    !_j( in(c,m); count(j) := count(j)  ).
  
  process mixer_open_publish = 
    let a = empty in
    out(c, empty).
end Dummy.

(*------------------------------------------------------------------*)
(* This system is exactly `Privacy_CCA` where we several
   processes after the initial voting phase by dummy processes. *)
system Blinding = 
   let vA  = diff(v0,v1) in
   let vB  = diff(v1,v0) in 
   let kcA = diff(kc0,kc1) in
   let kcB = diff(kc1,kc0) in
   let cmA = comm vA kcA in
   let cmB = comm vB kcB in
   Start  : out(c, <format (pk_enc sk_mix1), format (pk_enc sk_mix2)>);
   ( (A   : Alice_CCA (cmA,kcA,pkAdmin)                       )
   | (B   : Bob_CCA   (cmB,kcB,pkAdmin)                       ) 
   | (MVC : mixer_vote_collect_CCA(cmA,cmB,pkAdmin)           )
   | (MVP : Dummy.mixer_vote_publish                          )
   | (BBS : set_BB                                            )
   | (MOC : Dummy.mixer_open_collect                          )
   | (MOP : Dummy.mixer_open_publish                          )
 ).

(*------------------------------------------------------------------*)
namespace BlindingLeft.

lemma [Privacy_CCA/left, Blinding/left] exec_val (t:_): 
  happens(t) => exec@t = true.
Proof.
  induction t.
  intro *.
  case t;  try( intro Eq; rewrite /exec; by rewrite H).
  * auto.
  * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
  * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
Qed.

global lemma indist
  @set:Privacy_CCA
  @equiv:(Privacy_CCA/left, Blinding/left)
:
  [happens(Avote, Bvote)] ->
  equiv(
    tkA, tkB,  kc0, kc1, v0, v1,
    seedA_enc2,
    seedB_enc2,
    sk_mix2,
    sk_mix1,
    seedA_enc1,
    seedB_enc1,
    rdAdmin,
    frame@Avote, frame@Bvote
  ).
Proof. 
  intro Hap.
  trans [Privacy_CCA/left, Blinding/left]; 1,3: refl. 
  set t := if Avote < Bvote then Bvote else Avote.

  (* replace `frame@Avote` by `frame@t` *)
  ghave D: $( (frame@t) |> (frame@Avote)). { 
    ghave [] : [Avote < Bvote || not (Avote < Bvote)] by auto => A. 
    + by rewrite /t A /=; deduce. 
    + by rewrite /t A /=; deduce.
  }.
  deduce with D.
  clear D.

  (* replace `frame@Bvote` by `frame@t` *)
  ghave D: $( (frame@t) |> (frame@Bvote)). { 
    ghave [] : [Avote < Bvote || not (Avote < Bvote)] by auto => A. 
    + by rewrite /t A /=; deduce. 
    + by rewrite /t A /=; deduce.
  }.
  deduce with D.
  clear D.

  (* show that `happens t` *)
  have H : happens t. {
    ghave [] : [Avote < Bvote || not (Avote < Bvote)] by auto => A. 
    + by rewrite /t A.
    + by rewrite /t A.
  }.

  ghave H1 : [t <= Avote || t <= Bvote]. 
  {
    ghave [] : [Avote < Bvote || not (Avote < Bvote)] by auto => A. 
    + by right; rewrite /t A /=. 
    + by left; rewrite /t A /=. 
  }.

  (* prepare the induction hypothesis *)
  revert H H1.
  generalize t as t0. 
  clear t.
  
  induction => t IH Bound Hap0.
  case t; 
  try (
    intro H; 
    try destruct H;
    rewrite /frame /output exec_val /* //;
    by apply IH (pred t)
  ).
  - by intro ?. 

   (* Aopening *)
  - intro H. 
    have ? := Trace.Aopening_Avote. 
    have ? := Trace.Aopening_Bvote. 
    rewrite H in Bound. 
    case Bound; constraints.

   (* Bopening *)
  - intro H. 
    have ? := Trace.Bopening_Avote. 
    have ? := Trace.Bopening_Bvote. 
    rewrite H in Bound. 
    case Bound; constraints.

   (* MVP *)
  - intro H.
    have ? // := Trace.Avote_MVP _. 
    have ? // := Trace.Bvote_MVP _. 
    rewrite H in Bound. 
    case Bound; constraints.

   (* MOP *)
  - intro H.
    have ? // := Trace.any_MOP Avote _ _. 
    have ? // := Trace.any_MOP Bvote _ _. 
    rewrite H in Bound. 
    case Bound; constraints.
Qed.

end BlindingLeft.

(*------------------------------------------------------------------*)
namespace BlindingRight.

lemma [Blinding/right, Privacy_CCA/right] exec_val (t:_): 
  happens(t) => exec@t = true.
Proof.
  induction t.
  intro *.
  case t;  try( intro Eq; rewrite /exec; by rewrite H).
  * auto.
  * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
  * intro Eq. destruct Eq. rewrite /exec. by rewrite H.
Qed.

(* almost exact same proof as `BlindingLeft.indist` *)
global lemma indist
  @set:(Blinding/left, Privacy_CCA/right)
  @equiv:(Blinding/right, Privacy_CCA/right)
:
  [happens(Avote, Bvote)] ->
  equiv(
    tkA, tkB,  kc0, kc1, v0, v1,
    seedA_enc2,
    seedB_enc2,
    sk_mix2,
    sk_mix1,
    seedA_enc1,
    seedB_enc1,
    rdAdmin,
    frame@Avote, frame@Bvote
  ).
Proof. 
  intro Hap.
  trans [Blinding/right, Privacy_CCA/right]; 1,3: refl. 
  set t := if Avote < Bvote then Bvote else Avote.

  (* replace `frame@Avote` by `frame@t` *)
  ghave D: $( (frame@t) |> (frame@Avote)). { 
    ghave [] : [Avote < Bvote || not (Avote < Bvote)] by auto => A. 
    + by rewrite /t A /=; deduce. 
    + by rewrite /t A /=; deduce.
  }.
  deduce with D.
  clear D.

  (* replace `frame@Bvote` by `frame@t` *)
  ghave D: $( (frame@t) |> (frame@Bvote)). { 
    ghave [] : [Avote < Bvote || not (Avote < Bvote)] by auto => A. 
    + by rewrite /t A /=; deduce. 
    + by rewrite /t A /=; deduce.
  }.
  deduce with D.
  clear D.

  (* show that `happens t` *)
  have H : happens t. {
    ghave [] : [Avote < Bvote || not (Avote < Bvote)] by auto => A. 
    + by rewrite /t A.
    + by rewrite /t A.
  }.

  ghave H1 : [t <= Avote || t <= Bvote]. 
  {
    ghave [] : [Avote < Bvote || not (Avote < Bvote)] by auto => A. 
    + by right; rewrite /t A /=. 
    + by left; rewrite /t A /=. 
  }.

  (* prepare the induction hypothesis *)
  revert H H1.
  generalize t as t0. 
  clear t.
  
  induction => t IH Bound Hap0.
  case t; 
  try (
    intro H; 
    try destruct H;
    rewrite /frame /output exec_val /* //;
    by apply IH (pred t)
  ).
  - by intro ?. 

   (* Aopening *)
  - intro H. 
    have ? := Trace.Aopening_Avote. 
    have ? := Trace.Aopening_Bvote. 
    rewrite H in Bound. 
    case Bound; constraints.

   (* Bopening *)
  - intro H. 
    have ? := Trace.Bopening_Avote. 
    have ? := Trace.Bopening_Bvote. 
    rewrite H in Bound. 
    case Bound; constraints.

   (* MVP *)
  - intro H.
    have ? // := Trace.Avote_MVP _. 
    have ? // := Trace.Bvote_MVP _. 
    rewrite H in Bound. 
    case Bound; constraints.

   (* MOP *)
  - intro H.
    have ? // := Trace.any_MOP Avote _ _. 
    have ? // := Trace.any_MOP Bvote _ _. 
    rewrite H in Bound. 
    case Bound; constraints.
Qed.

end BlindingRight.

(*------------------------------------------------------------------*)
global lemma [Privacy_CCA] blinding :
  Let ub0 = unblind cm0 pkAdmin diff(tkA,tkB) diff(sA,sB) in
  Let ub1 = unblind cm1 pkAdmin diff(tkB,tkA) diff(sB,sA) in
  Let accA = baccepte cma pkAdmin tkA sA in 
  Let accB = baccepte cmb pkAdmin tkB sB in
  (* [happens(Avote,Bvote)] ->  *)
  [happens(MVP,MOP,BBS)] ->
  equiv(sk_mix1, sk_mix2,
    seedA_enc2, seedB_enc2, 
    cm0, cm1, kc0, kc1,
    if (acc_0 && acc_1) then ub0 else witness, 
    if (acc_0 && acc_1) then ub1 else witness, 
    seedA_enc1, seedB_enc1, bA, bB, 
    accA, accB, v0, v1, rdAdmin
  ).
Proof.
  have ? := Trace.happens_Avote.
  have ? := Trace.happens_Bvote.
  intro *.
  have -> : (acc_0 && acc_1) = (accA && accB). {
    rewrite /acc_0 /acc_1 /accA /accB /cm0 /cm1 /cma /cmb. 
    project. 
    - auto. 
    - by rewrite and_comm. 
  }. 

  (* prepare the way for the application of the blindness game, grouping `ub0` and `ub1` *)
  ghave A :
   $( 
     (accA, accB, if (accA && accB) then (ub0,ub1) else witness)
     |>
     (if (accA && accB) then ub0 else witness,
      if (accA && accB) then ub1 else witness)
    ) by deduce.
   deduce with A.
   clear A. 

   (* unfold all *)
   rewrite /*. clear.

   trans [Blinding/left, Privacy_CCA/right]; 3: refl. 
   apply BlindingLeft.indist; 1: auto.
   trans [Blinding/left, Blinding/right]; 
   [1: refl |
    3: apply BlindingRight.indist; 1:auto].

   (* fold back all *)
   set v0 := att' n_v0.
   set v1 := att' n_v1.
   set cm0 := comm v0 kc0.
   set cm1 := comm v1 kc1.
   set pkAdmin := read[pk_sign] (att' rdAdmin). 
   (* FIXME: we should be able to remove the type annotation *)
   set sA := read[bsigned] (input@Avote).
   set sB := read[bsigned] (input@Bvote).
   set cma := comm diff(v0, v1) diff(kc0, kc1).
   set cmb := comm diff(v1, v0) diff(kc1, kc0).
   set accA := baccepte cma pkAdmin tkA sA.
   set accB := baccepte cmb pkAdmin tkB sB.
   set bA := blind cma pkAdmin tkA.
   set bB := blind cmb pkAdmin tkB.
   set ub0 := unblind cm0 pkAdmin diff(tkA, tkB) diff(sA, sB).
   set ub1 := unblind cm1 pkAdmin diff(tkB, tkA) diff(sB, sA).

  crypto AdaptativeSelectiveFailureBlindness
    (m0 : cm0)
    (m1 : cm1)
    (pk : pkAdmin)
    (token0 : tkA)
    (token1 : tkB); 
   try auto.

  (* trace constraints *)
  - have ? := Trace.Bopening_Avote. 
    have ? := Trace.Bopening_Bvote. 
    constraints.

  (* trace constraints *)
  - have ? := Trace.Aopening_Avote. 
    have ? := Trace.Aopening_Bvote. 
    constraints.

  (* trace constraints *)
  - have ? := Trace.Bopening_Avote. 
    have ? := Trace.Bopening_Bvote. 
    constraints.

  (* trace constraints *)
  - have ? := Trace.Aopening_Avote. 
    have ? := Trace.Aopening_Bvote. 
    constraints.
Qed.
