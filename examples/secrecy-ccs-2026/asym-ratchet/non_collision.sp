(* In this files with presents many non-collision lemmas:
   The root key of `R` and `I` at two steps are differents,
   unless the two agent are syncronised and the root keys
   correspond to the same number of rachet steps.

   Since they are many lemmas between `RKRreceive`, `RKRsend`,
   `RKIreceive`, and `RKIsend`, we first introduce a notation
   to pinpoint a step in the racheting with a pair of an
   index and a boolean.
   Then we prove the non-collision lemmas with this notation.
   Finally, we rewrite these lemmas with the protocol macros,
   to be easier to use. *)
include Core.
include[admit] "indices.sp". 
include[admit] "DHLib.sp".
include[admit] "model.sp".
include[admit] "utils.sp".
include[admit] "trace.sp".

(* ------------------------------ *)

(******* Define the hashes chains *******)
(* We access states and sync with an index and a boolean to write our
   non-collision lemmas and perform an induction. *)
(*   stR 0 false   |   stR 0 true    |   stR 1 false   |   stR 1 true    | 
    RKRsend@init   | RKRreceive@R(1) |  RKRsend@R(1)   | RKRreceive@R(2) |
                   |                 |                 |                 |
         s_init       -->    h(...)     -->   h^2(...)    -->   h^3(...)    --> ...
                   |                 |                 |                 |
   RKIreceive@init |  RKIsend@init   | RKIreceive@I(1) |  RKIsend@I(1)   |
     stI 0 false   |   stI 0 true    |   stI 1 false   |   stI 1 true    |
                   |                 |                 |                 |
  *****************|*****************|*****************|*****************|*****
                   |                 |                 |                 |
      syncRI 0     |     syncIR 0    |     syncRI 1    |     syncIR 1    |
    sync 0 false   |   sync 0 true   |  sync 1 false   |   sync 1 true   |
                   |                 |                 |                 |   *)

(* `getR p` denotes the action in which role `R` performs the hash step denoted by `p`. *) 
let getR @system:S ((i,b) : index * bool) =
  if b then
    R (ind_succ i)
  else if i = ind_zero then
    init
  else
    R i.

(* Similar to `getR` *)
let getI @system:S ((i,b) : index * bool) =
  if i = ind_zero then
    init
  else
    I i.

(* Value of the hash stored by role `R` at the step denoted by `p`. *)
let stR @system:S ((i,b) : index * bool) =
  if b then
    RKRreceive@(getR (i,b))
  else
    RKRsend@(getR (i,b)).

(* Similar to `stR` *)
let stI @system:S ((i,b) : index * bool) =
  if b then
    RKIsend@(getI (i,b))
  else
    RKIreceive@(getI (i,b)).

(* `sync p` holds if the receiving agent is `sync` at the step `p` *)
(* TODO : Maybe it the sending agent. Need to write the lemma *)
let sync @system:S ((i,b) : index * bool) =
  if b then
    syncIR i
  else
    syncRI i.

(* Lemmas *)

(* Links order of pairs and oreder of timestamps *)
lemma pair_happensR @system:S : forall (p, p' : index * bool),
  happens(getR p') => p < p' => getR p <= getR p'.
Proof.
  intro p p'.
  rewrite /getR pair_order.
  smt ~no_macros.
Qed.


lemma pair_happensI @system:S : forall (p, p' : index * bool),
  happens(getI p') => p < p' => getI p <= getI p'.
Proof.
  intro p p'.
  rewrite /getI pair_order /=.
  smt ~no_macros.
Qed.

(* Technical lemma stating that [stR p] is obtained by hashing [stR
   (pair_pred p)] and something computed by the protocol (a p-time
   term using correctly the key [k], i.e. conditions required by
   collision). *)
lemma stR_pred @system:S : forall (p : index * bool),
  p <> pair_init =>
  happens(getR p) =>
  let j = choose (fun i => R i = getR p) in
  let x = if (p#2) then
             gRecR@getR p
          else
             gSendR@getR p
  in
  stR p = h(<stR (pair_pred p), ofG x>, k).
Proof.
  intro p H1 Hap j x.
  have C : p = (ind_zero, true) ||
           (exists i, p = (i, false) && i <> ind_zero) ||
           (exists i, p = (i, true) && i <> ind_zero); 1: smt.
  destruct C as [H2 | [[i[H2 H3]] | [i[H2 H3]]]].
  - rewrite /x  H2 /pair_pred /stR /getR /= in *.
    rewrite /RKRreceive /RKRsend /=.
    rewrite init_RKRsend; smt ~no_macros.
  - rewrite /x  H2 /pair_pred /stR /getR /= in *.
    rewrite if_false in *; 1,2: auto.
    smt.
  - rewrite /x  H2 /pair_pred /stR /getR /= in *.
    rewrite if_false in *; 1: auto.
    rewrite /RKRreceive.
    by rewrite (same_RKRsend (R i) (R (ind_succ i))); 1,2: smt ~no_macros.
Qed.

(* Similar to `stR_pred *)
lemma stI_pred @system:S : forall (p : index * bool),
  p <> pair_init =>
  happens(getI p) =>
  let j = choose (fun i => I i = getI p) in
  let x = if p#1 = ind_zero then
             g^(skR ind_zero)^(skI ind_zero)
          else if (p#2) then
             gSendI@getI p
          else
             gRecI@getI p
  in
  stI p = h(<stI (pair_pred p), ofG x>, k).
Proof.
  intro p H1 Hap j x.
  have C : p = (ind_zero, true) ||
           (exists i, p = (i, false) && i <> ind_zero) ||
           (exists i, p = (i, true) && i <> ind_zero); 1: smt.
  destruct C as [H2 | [[i[H2 H3]] | [i[H2 H3]]]].
  - by rewrite /x H2 /pair_pred /stI /getI /= in *.
  - rewrite /x H2 /pair_pred /stI /getI /= in *.
    rewrite if_false in *; 1,2: auto.
    rewrite (if_false (i = ind_zero)) in *; 1: auto.
    rewrite /RKIreceive.
    case (ind_pred i = ind_zero); rewrite /=; intro H4.
    + rewrite init_RKIsend; smt ~no_macros.
    + by rewrite (same_RKIsend (I (ind_pred i)) (I i)); 1,2: smt ~no_macros.
  - rewrite /x H2 /pair_pred /stI /getI /= in *.
    rewrite if_false in *; 1,2: auto.
    rewrite if_false in *; 1: auto.
    by rewrite /RKIsend.
Qed.

(* FIXME : collision is unsound, I think.
   See example below. Collision should not apply to some variables (non-ptime variable?) *)
global lemma _ @system:S : Forall x y, [x<>y => h(x,k) <> h(y,k)].
Proof. 
  intro x y. intro H1 H2. collision H2.
  auto.
Qed.

(* Last update lemma adapted to pairs. *)

(* Indicate that each timestamp `tau` is precessed by an action `R i`
   or `init` and that this action correspond to `getR(i,true)` and
   `getR(j,false)` for some `i` and `j`. Exception: `init` does not
   correspond to any pair `getR(i,true)`, so the lemma has an
   exception for this case *)

lemma pair_prevR @system:S : forall (tau : timestamp) (b : bool),
  happens(tau) => 
  (b && forall tau' j, tau' <= tau => tau' <> R j) || 
  (** special case, because no pair point to `RKRreceive@init`*)
  (exists i, getR (i,b) <= tau && forall tau' j, getR (i,b) < tau' => tau' <= tau => tau' <> R j).
Proof.
  induction.
  intro tau IH b Hap.
  case (tau = init); [2: intro H1; case (exists i, tau = R i)].
  - intro H. 
    case b; intro I.
    + by left.
    + right.
      by exists ind_zero.
  - intro [i H2].
    right.
    case b; intro I.
    + exists (ind_pred i).
      smt.
    + exists i.
      smt.
  - intro H2.
    have IH0 := IH (pred tau) b _ _; 1,2: auto.
    clear IH.
    destruct IH0 as [[I H3] | [i [H3 H4]]].
    + left. 
      smt ~no_macros.
    + right.
      exists i.
      smt ~no_macros.
Qed.

(* Out-of-context: Generalize `same_RKRsend` *)
lemma same_RKRsend0 @system:S (tau, tau' : timestamp) :
  tau <= tau' =>
  (not (exists j, tau < R j && R j <= tau')) =>
  RKRsend@tau = RKRsend@tau'.
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = tau' || tau < tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case tau' ; 
    try (intro [i R]; by rewrite R /RKRsend).
  - auto.
  - auto.
  - intro [i F].
    have H0 : (false => RKRsend@(pred tau') = RKRsend@tau'); 1: auto.
    apply H0.
    clear H0.
    apply H.
    by exists i. 
Qed.

(* Specialize `pair_prevR` for `RKRsend`. *)
lemma pair_prev_RKRsend @system:S : forall (tau : timestamp),
  happens(tau) => exists i, getR (i,false) <= tau && RKRsend@tau = stR (i,false).
Proof.
  intro tau Hap.
  have H := pair_prevR tau false Hap.
  destruct H as [[F H1] | [i [H1 H2]]]; 1: auto.
  exists i.
  split; 1: auto.
  by have H3 := same_RKRsend0 (getR (i,false)) tau H1 _; 1: smt ~no_macros.
Qed.

(* Out-of-context: Generalize `same_RKRreceive` *)
lemma same_RKRreceive0 @system:S (tau, tau' : timestamp) :
  tau <= tau' =>
  (not (exists j, tau < R j && R j <= tau')) =>
  RKRreceive@tau = RKRreceive@tau'.
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = tau' || tau < tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case tau' ; 
    try (intro [i R]; by rewrite R /RKRreceive).
  - auto.
  - auto.
  - intro [i F].
    have H0 : (false => RKRreceive@(pred tau') = RKRreceive@tau'); 1: auto.
    apply H0.
    clear H0.
    apply H.
    by exists i.
Qed.

(* Out-of-context *)
lemma init_RKRreceive0 @system:S : forall tau,
  happens (tau) =>
 (not (exists j, R j <= tau)) =>
  RKRreceive@tau = s_dum.
Proof.
  induction.
  intro tau IH Hap H.
  case (tau = init); 2: case(exists i, tau = R i).
  - auto.
  - intro [i T] T2.
    have F : exists j, R j <= tau; 1: by exists i.
    smt ~no_macros.
  - intro T1 T2.
    have R1 : RKRreceive@tau = RKRreceive@(pred tau); 1: case tau; auto + smt.
    have R2 := IH (pred tau) _ _; auto + smt ~no_macros.
Qed.

(* Specicialize `pair_prevR` for `RKRreceive`. *)
lemma pair_prev_RKRreceive @system:S : forall (tau : timestamp),
  happens(tau) => 
  (RKRreceive@tau = s_dum 
    || (exists i, getR (i,true) <= tau && RKRreceive@tau = stR (i,true))).
Proof.
  intro tau Hap.
  have H := pair_prevR tau true Hap.
  destruct H as [[I H1] | [i [H1 H2]]].
  - left.
    apply init_RKRreceive0; 1:auto.
    smt ~no_macros.
  - right.
    exists i.
    split; 1: auto.
    rewrite /stR /getR /= in *.
    rewrite eq_sym.
    apply same_RKRreceive0; 1: auto.
    smt ~no_macros.
Qed.

(* Similar for I. *)
lemma pair_prevI @system:S : forall (tau : timestamp) (b : bool),
  happens(tau) => exists i, getI (i,b) <= tau && forall tau' j, getI (i,b) < tau' => tau' <= tau => tau' <> I j.
Proof.
  induction.
  intro tau IH b Hap.
  case (tau = init); [2: intro H1; case (exists i, tau = I i)].
  - intro H.
    by exists ind_zero.
  - intro [i H2].
    exists i.
    smt.
  - intro H2.
    have IH0 := IH (pred tau) b _ _; 1,2: auto.
    clear IH.
    destruct IH0 as [i [H3 H4]].
    exists i.
    smt ~no_macros.
Qed.

(* Out-of-context: Generalize `same_RKIsend` *)
lemma same_RKIsend0 @system:S (tau, tau' : timestamp) :
  tau <= tau' =>
  (not (exists j, tau < I j && I j <= tau')) =>
  RKIsend@tau = RKIsend@tau'.
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = tau' || tau < tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case tau' ; 
    try (intro [i R]; by rewrite R /RKIsend).
  - auto.
  - auto.
  - intro [i F].
    have H0 : (false => RKIsend@(pred tau') = RKIsend@tau'); 1: auto.
    apply H0.
    clear H0.
    apply H.
    by exists i. 
Qed.

lemma pair_prev_RKIsend @system:S : forall (tau : timestamp),
  happens(tau) => 
     exists i, getI (i,false) <= tau && RKIsend@tau = stI (i,true).
Proof.
  intro tau Hap.
  have H := pair_prevI tau false Hap.
  destruct H as [i [H1 H2]].
  exists i.
  split; 1: auto.
  by have H3 := same_RKIsend0 (getI (i,false)) tau H1 _; 1: smt ~no_macros.
Qed.

(* Out-of-context: Generalize `same_RKIreceive` *)
lemma same_RKIreceive0 @system:S (tau, tau' : timestamp) :
  tau <= tau' =>
  (not (exists j, tau < I j && I j <= tau')) =>
  RKIreceive@tau = RKIreceive@tau'.
Proof.
  induction tau'.
  intro tau' IH I H.
  have C : tau = tau' || tau < tau'; 1: auto.
  case C; 1: auto.
  rewrite (IH (pred tau')); 2,3: auto. {
    intro [j H2].
    apply H.
    by exists j.
  }
  case tau' ; 
    try (intro [i R]; by rewrite R /RKIreceive).
  - auto.
  - auto.
  - intro [i F].
    have H0 : (false => RKIreceive@(pred tau') = RKIreceive@tau'); 1: auto.
    apply H0.
    clear H0.
    apply H.
    by exists i.
Qed.

lemma pair_prev_RKIreceive @system:S : forall (tau : timestamp),
  happens(tau) => 
     exists i, getI (i,false) <= tau && RKIreceive@tau = stI (i,false).
Proof.
  intro tau Hap.
  have H := pair_prevI tau true Hap.
  destruct H as [i [H1 H2]].
  exists i.
  split; 1: auto.
  rewrite /stI /getI /= in *.
  rewrite eq_sym.
  apply same_RKIreceive0; 1: auto.
  smt ~no_macros.
Qed.

(* Sync lemmas adapted to pairs *)
lemma sync_pred @set:S :
  forall p p', p <= p' => sync p' => sync p.
Proof.
  intro p p'.
  induction p'.
  intro p' IH I S.
  case (p = p'); 1: auto.
  intro C.
  simpl.
  rewrite le_lt in I; 1: auto.
  apply IH (pair_pred p') _ _. {
    apply pair_order_pred3 p p' I.
  } {
    apply pair_order_pred1 p'.
    intro F.
    apply pair_order_min p.
    by rewrite F in I.
  }
  rewrite /pair_pred /sync in *.
  case (p'#2) ; intro P; simpl.
  - rewrite /syncIR if_true in S; 1: auto.
    smt.
  - rewrite /syncRI if_false in S; 1: auto.
    have M := pair_order_min p.
    case S; 2: auto.
    have H : p' = pair_init. {
      rewrite /pair_init. smt ~no_macros.
    }
    rewrite H in *.
    clear IH P S H.
    have H := le_impl_eq_lt p pair_init.
    smt ~no_macros.
Qed.



(* ------------------------------ *)
(***** Non-collision for pairs ****)

(******* Preimage resistance *******)
(* This is the initial case for a future induction:
   We use the Preimage resistance game to prove that the hashes chains
   cannot loop back to their initial value `s_init`.
   We have the same lemmas for the dummy value `s_dum`. *)

lemma PIR_R @set:S/left @equiv:(S/left, S/left) : forall (p : index * bool),
  happens(getR p) => p <> pair_init => stR p <> s_init.
Proof.
  intro p Hap H.
  rewrite stR_pred /=; 1,2: auto.
  case (p#2).
  - intro P1.
    have P2 : p = (p#1, true); 1: smt ~no_macros.
    rewrite P2 /pair_pred /stR /getR /= in *.
    ghave Main : equiv(diff(h(<RKRsend@(if (p#1 = ind_zero) then init else R(p#1)),
                               ofG (gRecR@R(ind_succ (p#1)))>, k) <>
                            s_init, true)). 
    {
      crypto PIR (goal:s_init) (k:k).
    }
    by rewrite equiv Main.
  - intro P1.
    have P2 : p = (p#1, false); 1: smt ~no_macros.
    rewrite P2 /pair_pred /stR /getR /= in *.
    rewrite /pair_init in H.
    have P3 : (p#1 = ind_zero) = false; 1: smt ~no_macros.
    rewrite P3 if_false in *; 1,2: auto.
    have P4 : ind_succ (ind_pred (p#1)) = p#1; 1: smt ~no_macros.
    rewrite P4.
    ghave Main : equiv(diff(h (<RKRreceive@R(p#1),
                                ofG (gSendR@R(p#1))>, k) <>
                            s_init, true)).
    {
      crypto PIR (goal:s_init) (k:k).
    }
    by rewrite equiv Main.
Qed.

lemma PIR_I @set:S/left @equiv:(S/left, S/left) : forall (p : index * bool),
  happens(getI p) => p <> pair_init => stI p <> s_init.
Proof.
  intro p Hap H.
  rewrite stI_pred /=; 1,2: auto.
  case (p#2).
  - intro P1.
    have P2 : p = (p#1, true); 1: smt ~no_macros.
    rewrite P2 /pair_pred /stI /getI /= in *.
    case (p#1 = ind_zero).
    + intro P3.
      rewrite /= /RKIreceive in *.
      ghave Main : equiv(diff(h (<s_init,ofG (g ^ (skR ind_zero ** skI ind_zero))>, k) <>
                                 s_init, true)). 
      {
        crypto PIR (goal:s_init) (k:k).
      }
      by rewrite equiv Main.
    + intro P3.
      rewrite if_false in *; 1,2: auto.
      rewrite if_false; 1: auto.
      ghave Main : equiv(diff(h (<RKIreceive@I(p#1),ofG (gSendI@I(p#1))>, k) <>
                              s_init , true)). 
      {
        crypto PIR (goal:s_init) (k:k).
      }
      by rewrite equiv Main.
  - intro P1.
    have P2 : p = (p#1, false); 1: smt ~no_macros.
    rewrite P2 /pair_pred /stI /getI /= in *.
    rewrite /pair_init in H.
    have P3 : (p#1 = ind_zero) = false; 1: smt ~no_macros.
    rewrite P3 /= in *.
    ghave Main : equiv(diff(h(<RKIsend@(if (ind_pred (p#1) = ind_zero) then
                                           init else I(ind_pred (p#1))),
                              ofG (gRecI@I(p#1))>, k) <>
                            s_init, true)).
    {
      crypto PIR (goal:s_init) (k:k).
    }
    by rewrite equiv Main.
Qed.

lemma PIR_R_dum @set:S/left @equiv:(S/left, S/left) : forall (p : index * bool),
  happens(getR p) => stR p <> s_dum.
Proof.
  intro p Hap.
  case (p = pair_init); intro H.
  - rewrite H.
    expandall.
    rewrite /= /RKRsend.
    intro F.
    fresh F.
  - rewrite stR_pred /=; 1,2: auto.
    case (p#2).
    + intro P1.
      have P2 : p = (p#1, true); 1: smt ~no_macros.
      rewrite P2 /pair_pred /stR /getR /= in *.
      ghave Main : equiv(diff(h(<RKRsend@(if (p#1 = ind_zero) then init else R(p#1)),
                                 ofG (gRecR@R(ind_succ (p#1)))>, k) <>
                              s_dum , true)).
      {
        crypto PIR (goal:s_dum) (k:k).
      }
      by rewrite equiv Main.
    + intro P1.
      have P2 : p = (p#1, false); 1: smt ~no_macros.
      rewrite P2 /pair_pred /stR /getR /= in *.
      rewrite /pair_init in H.
      have P3 : (p#1 = ind_zero) = false; 1: smt ~no_macros.
      rewrite P3 if_false in *; 1,2: auto.
      have P4 : ind_succ (ind_pred (p#1)) = p#1; 1: smt ~no_macros.
      rewrite P4.
      ghave Main : equiv(diff(h (<RKRreceive@R(p#1),
                                ofG (gSendR@R(p#1))>, k) <>
                            s_dum, true)).
    {
      crypto PIR (goal:s_dum) (k:k).
    }
    by rewrite equiv Main.
Qed.

lemma PIR_I_dum @set:S/left @equiv:(S/left, S/left) : forall (p : index * bool),
  happens(getI p) => stI p <> s_dum.
Proof.
  intro p Hap.
  case (p = pair_init); intro H.
  - rewrite H.
    expandall.
    rewrite /= /RKIreceive.
    intro F.
    fresh F.
  - rewrite stI_pred /=; 1,2: auto.
    case (p#2).
    + intro P1.
      have P2 : p = (p#1, true); 1: smt ~no_macros.
      rewrite P2 /pair_pred /stI /getI /= in *.
      case (p#1 = ind_zero).
      * intro P3.
        rewrite if_true in *; 1,2: auto.
        rewrite if_true; 1: auto.
        rewrite /RKIreceive.
        ghave Main : equiv(diff(h (<s_init,ofG (g ^ (skR ind_zero ** skI ind_zero))>, k) <>
                                s_dum, true)).
        {
          crypto PIR (goal:s_dum) (k:k).
        }
        by rewrite equiv Main.
      * intro P3.
        rewrite if_false in *; 1,2: auto.
        rewrite if_false; 1: auto.
        ghave Main : equiv(diff(h (<RKIreceive@I(p#1),ofG (gSendI@I(p#1))>, k) <>
                                s_dum  , true)).
        {
          crypto PIR (goal:s_dum) (k:k).
        }
        by rewrite equiv Main.
    + intro P1.
      have P2 : p = (p#1, false); 1: smt ~no_macros.
      rewrite P2 /pair_pred /stI /getI /= in *.
      rewrite /pair_init in H.
      have P3 : (p#1 = ind_zero) = false; 1: smt ~no_macros.
      rewrite P3 (if_false false); 1: auto.
      rewrite (if_false false); 1: auto.
      rewrite if_false in Hap; 1: auto.
      ghave Main : equiv(diff(h(<RKIsend@(if (ind_pred (p#1) = ind_zero)
                                          then init else I(ind_pred (p#1))),
                                 ofG (gRecI@I(p#1))>, k) <>
                              s_dum, true)).
    {
      crypto PIR (goal:s_dum) (k:k).
    }
    by rewrite equiv Main.
Qed.



(******* Main NoCol lemmas *******)

(* We have four main lemmas for non-collision :
   - [NoColR]: Non-collision on the chain stR at different step
   - [NoColI]: Non-collision on the chain stI at different step
   - [NoColRI]: Non-collision between stR and stI at different step
   - [NoColRIsync]: Non-collision between stR and stI at the same step if sync is false. *)

lemma NoColR @set:S/left : forall (p, p' : index * bool),
  happens(getR p, getR p') => p <> p' => stR p <> stR p'.
Proof.
  have Main : forall (p, p0' : index * bool), happens(getR p0') => p < p0' => stR p <> stR p0'. {
    intro p p'.
    generalize p.
    induction p'.
    intro p' IH p Hap Ord.
    have P : p = pair_init || p <> pair_init; 1: auto.
    have P' : p' = pair_init || p' <> pair_init; 1: auto.
    case P'; 2: case P.
    - rewrite P' in Ord.
      have F := pair_order_min p.
      smt ~no_macros.
    - have H : stR p = s_init; 1: by rewrite P /stR /pair_init /getR /= /RKRsend.
      rewrite H neq_sym.
      by apply PIR_R.
    - rewrite (stR_pred p); 2: auto. {
        have H := pair_happensR p p'.
        smt ~no_macros.
      }
      rewrite (stR_pred p'); 1,2: auto.
      intro F.
      collision F.
      clear F.
      intro F.
      apply (f_apply fst) in F.
      rewrite /= in F.
      have IH0 := IH (pair_pred p') (pair_pred p) _ _ _. {
        by apply pair_order_pred2 p p'.
      } {
        have Ord2 := pair_order_pred1 p'.
        have Hap2 := pair_happensR (pair_pred p') p'.
        smt ~no_macros.
      } {
        by apply pair_order_pred1 p'.
      }
      auto.
  }
  intro p p' Hap H.
  have C := pair_order_tricho p p'.
  case C.
  - auto.
  - by have _ := Main p p' _ _.
  - by have _ := Main p' p _ _.
Qed.

lemma NoColI @set:S/left : forall (p, p' : index * bool),
  happens(getI p, getI p') => p <> p' => stI p <> stI p'.
Proof.
  have Main : forall (p, p0' : index * bool), happens(getI p0') => p < p0' => stI p <> stI p0'. {
    intro p p'.
    generalize p.
    induction p'.
    intro p' IH p Hap Ord.
    have P : p = pair_init || p <> pair_init; 1: auto.
    have P' : p' = pair_init || p' <> pair_init; 1: auto.
    case P'; 2: case P.
    - rewrite P' in Ord.
      have F := pair_order_min p.
      smt ~no_macros.
    - have H : stI p = s_init; 1: by rewrite P /stI /pair_init /getI /= /RKIreceive.
      rewrite H neq_sym.
      by apply PIR_I.
    - rewrite (stI_pred p); 2: auto. {
        have H := pair_happensI p p'.
        smt ~no_macros.
      }
      rewrite (stI_pred p'); 1,2: auto.
      intro F.
      collision F.
      clear F.
      intro F.
      apply (f_apply fst) in F.
      rewrite /= in F. 
      have IH0 := IH (pair_pred p') (pair_pred p) _ _ _.
        { by apply pair_order_pred2 p p'.
      } { smt.
      } { by apply pair_order_pred1 p'.
      }
      auto.
  }
  intro p p' Hap H.
  have C := pair_order_tricho p p'.
  case C.
  - auto.
  - by have _ := Main p p' _ _.
  - by have _ := Main p' p _ _.
Qed.

lemma NoColRI @set:S/left : forall (p, p' : index * bool),
  happens(getR p, getI p') => p <> p' => stR p <> stI p'.
Proof.
  intro p.
  induction p.
  intro p IH p' Hap D.
  have P' : p' = pair_init || p' <> pair_init; 1: auto.
  have P : p = pair_init || p <> pair_init; 1: auto.
  case P'; case P.
  - auto.
  - have H : stI p' = s_init; 1: by rewrite P' /stI /pair_init /getI /= /RKIreceive.
    rewrite H.
    by apply PIR_R.
  - have H : stR p = s_init; 1: by rewrite P /stR /pair_init /getR /= /RKRsend.
    rewrite H neq_sym.
    by apply PIR_I.
  - rewrite (stR_pred p); 1,2: auto.
    rewrite (stI_pred p'); 1,2: auto.
    intro F.
    collision F.
    clear F.
    intro F.
    apply (f_apply fst) in F.
    rewrite /= in F.
    have IH0 := IH (pair_pred p) (pair_pred p') _ _ _. {
      rewrite /pair_pred.
      smt.
    } {
      have Ord1 := pair_order_pred1 p.
      have Hap1 := pair_happensR (pair_pred p) p.
      have Ord2 := pair_order_pred1 p'.
      have Hap2 := pair_happensI (pair_pred p') p'.
      smt ~no_macros.
    } {
      by apply pair_order_pred1.
    }
    auto.
Qed.



lemma NoColRIsync @set:S/left : forall (p : index * bool),
  happens(getR p, getI p) => not(sync p) => stR p <> stI p.
Proof.
  intro p.
  induction p.
  intro p IH Hap S.
  case (p = pair_init); intro C.
  - rewrite C in *.
    rewrite /sync /pair_init /syncRI /= in S.
    auto.
  - rewrite stR_pred; 1,2: auto.
    rewrite stI_pred; 1,2: auto.
    intro F.
    collision F.
    clear F.
    intro F.
    case (sync (pair_pred p)); intro S2.
    + clear IH.
      apply f_apply snd in F.
      simpl.
      rewrite /sync in S.
      rewrite /sync /pair_pred /= in S2.
      case (p#2); intro C2.
      * rewrite (if_true (p#2)) in *; 1,2,3,4: auto.
        rewrite /getR if_true in F; 1: auto.
        rewrite /gRecR in F.
        simpl.
        rewrite /syncIR not_or !not_and in S.
        have [[S0 S1] | [S0 S1] | [S0 S1]] :
          (p#1 = ind_zero && gI@R(ind_one) <> g ^ skI ind_zero) ||
          (p#1 <> ind_zero &&
            gRecR@R(ind_succ (p#1)) <> gSendI@I(p#1)) ||
          (p#1 <> ind_zero && not (I(p#1) < R(ind_succ (p#1))));
          [1: smt ~no_macros | 2,3,4: clear S].
        -- rewrite if_true in F; 1: auto.
           rewrite S0 in Hap.
           rewrite S0 -ind_o ind_pred_one E_com -exp_mult in F.
           by apply inv_exp in F.
        -- rewrite if_false in F; 1: auto.
           rewrite if_true in F; 1: auto.
           rewrite /getI (if_false) in *; 1,2: auto.
           by rewrite -F /gRecR in S1.
        -- rewrite if_false in F; 1: auto.
           rewrite if_true in F; 1: auto.
           rewrite /getI (if_false) in *; 1,2: auto.
           rewrite ind_pred_succ in F; 1: smt.
           rewrite /gSendI in F.
           apply (f_apply dlog) in F.
           rewrite (dlog_exp _ (skI(p#1))) in F.
           apply (f_apply (fun x => (inv_E (dlog (gR@I(p#1)))) ** x)) in F.
           rewrite /= !-E_assoc inv_E_ax_l E_e_mult_r in F.
           fresh F; [1,2,5: auto | 3,4: smt ~no_macros].
      * have I : p#1 <> ind_zero; 1: smt.
        rewrite !(if_false (p#1 = ind_zero)) in *; 1,2,3: auto.
        rewrite !(if_false (p#2)) in *; 1,2,3,4,5,6: auto.
        rewrite (if_false (p#1 = ind_zero)) in *; 1,2: auto.
        rewrite /= in S2.
        rewrite /syncRI not_or !not_and in S.
        destruct S as [H [S|S|S]]; 2,3: auto.
        clear H.
        rewrite /gSendR in F.
        apply (f_apply dlog) in F.
        rewrite (dlog_exp _ (skR(p#1))) in F.
        apply (f_apply (fun x => (inv_E (dlog (gI@R(p#1)))) ** x)) in F.
        rewrite /= !-E_assoc inv_E_ax_l E_e_mult_r in F.
        fresh F; [1,2,5: auto | 3,4: smt ~no_macros]. 
    + apply f_apply fst in F.
      simpl.
      have IH0 := IH (pair_pred p) _ _ S2; [1: smt | 3: auto].
      by apply pair_order_pred1.
Qed.



(* ------------------------------ *)
(******* Exported lemmas *******)
(* We write the non-collision lemmas expressed with pairs
   as lemmas using the protocol macros. *)

lemma NoColRKRsend  @set:S/left (i,j : index) :
  happens(R i, R j) => i <> j => RKRsend@(R i) <> RKRsend@(R j).
Proof.
  intro Hap H.
  have NoCol := NoColR (i, false) (j, false).
  smt.
Qed.

lemma NoColRKIreceive @set:S/left (i,j : index) :
  happens(I i, I j) => i <> j => RKIreceive@(I i) <> RKIreceive@(I j).
Proof.
  intro Hap H.
  have NoCol := NoColI (i, false) (j, false).
  smt.
Qed.

lemma NoColRKRreceive  @set:S/left (i,j : index) :
  happens(R i, R j) => i <> j => RKRreceive@(R i) <> RKRreceive@(R j).
Proof.
  intro Hap H.
  have NoCol := NoColR (ind_pred i, true) (ind_pred j, true).
  smt.
Qed.

lemma NoColRKIsend @set:S/left (i,j : index) :
  happens(I i, I j) => i <> j => RKIsend@(I i) <> RKIsend@(I j).
Proof.
  intro Hap H.
  have NoCol := NoColI (i, true) (j, true).
  smt.
Qed.

lemma NoColRKIsendIzero @set:S/left (i : index) :
  happens(I i) => RKIsend@(I i) <> RKIsend@(pred Izero).
Proof.
  intro Hap.
  have Init : pred Izero = init; 1: smt ~no_macros.
  have NoCol := NoColI (i, true) (ind_zero, true).
  smt.
Qed.

lemma NoColRKIreceiveIzero @set:S/left (i : index) :
  happens(I i) => RKIreceive@(I i) <> RKIreceive@(pred Izero).
Proof.
  intro Hap.
  have Init : pred Izero = init; 1: smt ~no_macros.
  have NoCol := NoColI (i, false) (ind_zero, false).
  smt.
Qed.

lemma NoColRKRsendRKIsend @set:S/left (tau, tau' : timestamp) :
  happens(tau, tau') => RKRsend@tau <> RKIsend@tau'.
Proof.
  intro Hap.
  have P1 := pair_prev_RKRsend tau. (*Cannot write `_` at the end?*)
  have H1 := P1 _; 1: auto.
  destruct H1 as [i1 [Ord1 H1]].
  rewrite H1.
  clear P1 H1.
  have P2 := pair_prev_RKIsend tau'.
  have H2 := P2 _; 1: auto.
  destruct H2 as [i2 [Ord2 H2]].
  rewrite H2.
  clear P2 H2.
  by apply NoColRI (i1, false) (i2, true).
Qed.

lemma NoColRKRreceiveRKIreceive @set:S/left  (tau, tau' : timestamp) :
  happens(tau, tau') => RKRreceive@tau <> RKIreceive@tau'.
Proof.
  intro Hap.
  have P2 := pair_prev_RKIreceive tau'.
  have H2 := P2 _; 1: auto.
  destruct H2 as [i2 [Ord2 H2]].
  rewrite H2.
  clear P2 H2.
  have P1 := pair_prev_RKRreceive tau.
  have H1 := P1 _; 1: auto.
  destruct H1 as [H1 | [i1 [Ord1 H1]]]; rewrite H1; clear H1 P1.
  - rewrite neq_sym.
    by apply PIR_I_dum.
  - by apply NoColRI (i1, true) (i2, false).
Qed.

lemma NoColRKRsendRKRreceive @set:S/left (tau, tau' : timestamp) :
  happens(tau, tau') => RKRsend@tau <> RKRreceive@tau'.
Proof.
  intro Hap.
  have P1 := pair_prev_RKRsend tau.
  have H1 := P1 _; 1: auto.
  destruct H1 as [i1 [Ord1 H1]].
  rewrite H1.
  clear P1 H1.
  have P2 := pair_prev_RKRreceive tau'.
  have H2 := P2 _; 1: auto.
  destruct H2 as [H2 | [i2 [Ord2 H2]]]; rewrite H2; clear H2 P2.
  - by apply PIR_R_dum.
  - by apply NoColR (i1, false) (i2, true).
Qed.

lemma NoColRKIsendRKIreceive @set:S/left  (tau, tau' : timestamp) :
  happens(tau, tau') => RKIsend@tau <> RKIreceive@tau'.
Proof.
  intro Hap.
  have P1 := pair_prev_RKIsend tau.
  have H1 := P1 _; 1: auto.
  destruct H1 as [i1 [Ord1 H1]].
  rewrite H1.
  clear P1 H1.
  have P2 := pair_prev_RKIreceive tau'.
  have H2 := P2 _; 1: auto.
  destruct H2 as [i2 [Ord2 H2]].
  rewrite H2.
  clear H2 P2.
  by apply NoColI (i1, true) (i2, false).
Qed.

lemma NoColIThenR @set:S/left (i,j : index) :
  I j < R i => RKRsend@(R i) <> RKIreceive@(I j).
Proof.
  intro Hap.
  case (i=j).
  - intro H F1.
    rewrite /RKRsend /RKIreceive in F1.
    collision F1.
    intro F2.
    apply f_apply snd in F2.
    simpl. (* It applies `ofG_inj` *)
    rewrite /gSendR /gRecI in F2.

    apply f_apply dlog in F2.
    apply f_apply (fun x => x ** (inv_E (dlog (gI@R(i))))) in F2.
    simpl.
    rewrite E_com -E_assoc inv_E_ax_l E_e_mult_r in F2.
    fresh F2; smt ~no_macros.
  - intro H.
    have R1 : stR(i, false) = RKRsend@(R i); 1: smt.
    have R2 : stI(j, false) = RKIreceive@(I j); 1: smt.
    rewrite -R1 -R2.
    apply NoColRI; [1: smt | 2: auto].
Qed.

lemma NoColRThenI @set:S/left (i,j : index) :
  R j < I i => RKIsend@(I i) <> RKRreceive@(R j).
Proof.
  intro Hap.
  case (i = ind_pred j).
  - intro H F1.
    rewrite /RKIsend /RKRreceive in F1.
    collision F1.
    intro F2.
    apply f_apply snd in F2.
    simpl. (* It applies `ofG_inj` *)
    rewrite /gSendI /gRecR in F2.

    apply f_apply dlog in F2.
    apply f_apply (fun x => x ** (inv_E (dlog (gR@I i)))) in F2.
    simpl.
    rewrite E_com -E_assoc inv_E_ax_l E_e_mult_r in F2.
    fresh F2; smt ~no_macros.
  - intro H.
    have R1 : stR(ind_pred j, true) = RKRreceive@(R j). {
      rewrite /stR /getR /=.
      smt ~no_macros.
    }
    have R2 : stI(i, true) = RKIsend@(I i). {
      rewrite /stI /getI /=.
      smt ~no_macros.
    }
    rewrite -R1 -R2 neq_sym.
    apply NoColRI; [1: smt | 2: auto].
Qed.





(******* Exported lemmasSync lemmas v2 *******)

lemma SyncIoth2 @set:S (p: index*bool) :
  happens(getR p) => happens(getI p) => sync p => stR p = stI p.
Proof.
  induction p.
  intro p IH HapR HapI Sync.
  have P : p = (p#1, p#2); 1: smt ~no_macros.
  case (p#1 = ind_zero); case p#2; intro C2; intro C1.
  - have GR : getR p = R (ind_one); 1: smt.
    have GI : getI p = init; 1: smt.
    rewrite /sync /= if_true in Sync; 1:auto.
    rewrite /syncIR in Sync.
    rewrite /stR /stI /= if_true; 1: auto.
    rewrite -P GR if_true /=; 1: auto.
    rewrite GI.
    rewrite /RKRreceive /RKIsend.
    rewrite /gRecR.
    rewrite init_RKRsend; 1: auto.
    have H : (gI@R(ind_one) = g ^ skI ind_zero); 1: smt ~no_macros.
    rewrite H exp_mult E_com -exp_mult.
    smt ~no_macros.
  - have GR : getR p = init; 1: smt.
    have GI : getI p = init; 1: smt.
    rewrite /stR /stI -P GR GI /RKRsend /RKIreceive.
    smt ~no_macros.
  - have GR : getR p = R (ind_succ (p#1)); 1: smt.
    have GI : getI p = I (p#1); 1: smt.
    rewrite /sync /= if_true in Sync; 1:auto.
    rewrite /syncIR in Sync.
    case Sync; 1: smt ~no_macros.
    destruct Sync as [Sync1 [Sync2 Sync3]].
    rewrite /stR /stI /= if_true; 1: auto.
    rewrite -P GR if_true /=; 1: auto.
    rewrite GI.
    rewrite /RKRreceive /RKIsend Sync3.
    rewrite -(same_RKRsend0 (R(p#1)) (pred (R(ind_succ (p#1))))); 1,2: smt ~no_macros ~steps:130000.
    have IH0 := IH (p#1, false) _ _ _ _; [1,2,3: smt | 4: by rewrite pair_order].
    have STR : stR (p#1, false) = RKRsend@R(p#1); 1: smt.
    have STI : stI (p#1, false) = RKIreceive@I(p#1); 1: smt.
    rewrite STR STI in IH0.
    auto.
  - have GR : getR p = R (p#1); 1: smt.
    have GI : getI p = I (p#1); 1: smt.
    rewrite /sync /= if_false in Sync; 1:auto.
    rewrite /syncRI in Sync.
    case Sync; 1: smt ~no_macros.
    destruct Sync as [Sync1 [Sync2 Sync3]].
    rewrite /stR /stI /= if_false; 1: auto.
    rewrite -P GR if_false /=; 1: auto.
    rewrite GI.
    rewrite /RKRsend /RKIreceive Sync3.
    have IH0 := IH (ind_pred (p#1), true) _ _ _ _;
      [1,2,3: smt | 4: rewrite pair_order; smt ~no_macros].
    have STR : stR (ind_pred (p#1), true) = RKRreceive@R(p#1); 1: smt.
    rewrite -STR IH0.
    fa.
    fa; 2: auto.
    fa.
    rewrite /stI if_true /=; 1: auto.
    apply (same_RKIsend0 (getI (ind_pred (p#1), true)) (pred (I(p#1)))); 1: smt.
    intro [j [F1 F2]].
    rewrite /getI in F1.
    case (p#1 = ind_one). 
      +  intro Eq. clear IH. clear IH0. simpl.  rewrite Eq if_true in F1. by simpl.
        
        have U: I j < I((p#1)) by constraints. 
        apply contrapositive_orderI in U.  rewrite Eq in U.
        have C := I_bigger_one j _. constraints.
        case C. 
        ++ have _ := ind_irrefl ind_one. by simpl. 
        ++  apply ind_to_leq in C.  by apply ind_to_leq in U.
      + simpl.

        intro neq.  rewrite if_false in F1. simpl. intro Eq. 
        case p#1 =ind_one. 
        ++ intro Eq2. by simpl.
        ++ intro Neq.  search ind_pred _.  clear IH STR.   smt ~no_macros.
     
      
        simpl.
        have U: I j < I((p#1)) by constraints. 
        apply contrapositive_orderI in U.  
        apply contrapositive_orderI in F1.  
        search _ ~< _.
        apply ind_pred_order2 in U. 
        case U. 
         ++ rewrite U in F1. have _ := ind_irrefl (ind_pred (p#1)). by simpl. 
         ++ apply ind_to_leq in F1. apply ind_to_leq in U. by simpl. 
Qed.

lemma SyncRI2 @set:S i:
  i <> ind_zero => syncRI (i) => RKIreceive@I i = RKRsend@R i.
Proof.
  intro I Sync.
  have H := SyncIoth2 (i, false).
  rewrite /sync /stR /stI /getR /getI /= !if_false in H; 1,2: auto.
  rewrite /syncRI in Sync.
  have Hap : R i < I i; smt.
Qed.

lemma SyncIR2 @set:S i:
  i <> ind_zero => syncIR (i) => RKRreceive@R (ind_succ i) = RKIsend@I (i).
Proof.
  intro I Sync.
  have H := SyncIoth2 (i, true).
  rewrite /sync /stR /stI /getR /getI /= !if_false in H; 1: auto.
  rewrite /syncIR in Sync.
  have Hap : I i < R (ind_succ i); smt.
Qed.

lemma SyncIR_init @set:S :
  syncIR (ind_zero) => RKRreceive@R (ind_one) = RKIsend@init.
Proof.
  intro Sync.
  have H := SyncIoth2 (ind_zero, true).
  rewrite /sync /stR /stI /getR /getI /= in H.
  rewrite H; 1,2,4: auto.
  rewrite /syncIR in Sync.
  have S : gI@R(ind_one) = g ^ skI ind_zero; 1: smt ~no_macros.
  clear Sync H.
  expand ~def gI.
  expand ~def input.
  case (happens(R ind_one)); intro H.
  - smt ~no_macros.
  - rewrite if_true in S; 1: auto.
    apply f_apply dlog in S. search E_e.
    rewrite dlog_exp dlog_g E_e_mult_r in S.
    fresh S.
Qed.


lemma NoColRKRreceiveRKIsend @set:S/left  (i:index, tau : timestamp) :
  happens(R i, tau) => not(SyncIR (ind_pred i)) => (RKRreceive@R i <> RKIsend@tau).
Proof.
  intro Hap.
  have P1 := pair_prev_RKIsend tau.
  have [i0 [H1 H2]] := P1 _; 1: auto => {P1}.
  rewrite H2.

  have stR : RKRreceive@R(i)   = stR (ind_pred i, true).
   {
   rewrite /stR /=.  rewrite /getR. smt ~no_macros.
   }
  rewrite stR.
  case ind_pred i <> i0.
  ++ intro neq. 
     have _ := NoColRI (ind_pred i, true) (i0, true) _ _. auto. smt. 
     smt.
  ++ intro Eq.  rewrite Eq.
     intro Nsync.
     apply NoColRIsync. smt. rewrite -syncIR_to_SyncIR in Nsync. auto.
Qed.    


lemma NoColRKIreceiveRKRsend @set:S/left  (i,j:index) :
  happens(R i, I j) => not(SyncRI j) => (RKRsend@R i <> RKIreceive@I j).
Proof.
  intro Hap.

  case i <> j.
  ++ intro neq. 
     have _ := NoColRI (i, false) (j, false) _ _. auto. smt. 
     smt.
  ++ intro Eq.  rewrite Eq.
     intro Nsync.
     have _ := NoColRIsync (i,false). rewrite -syncRI_to_SyncRI in Nsync. smt. 
Qed.    
