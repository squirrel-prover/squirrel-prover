(* To prove that the attacker cannot use the frame to compute
   a secret value,  first we generalise the knowledge the
   attacker can access.
   This knowledge is given by a set of oracles.
   First, we define each oracle, before defining the two sets
   of oracles needed for the secrecy proof. *)
include Core.
include[admit] "indices.sp". 
include[admit] "DHLib.sp".
include[admit] "model.sp".
include[admit] "utils.sp".
include[admit] "trace.sp".

(* ------------------------------ *)

(************************************)
(************* Oracles **************)
(************************************)

(* 1) Oracles over which we perform the induction.
   They give root or chain keys computed by one of the agent
   until a given timestamp.
   The secrecy proof is based on an induction over these timstamps. *)

(* Healthy chain keys *)
let OCKRsend @system:S (tau:timestamp) =
  fun i => if R i <= tau && (HealthyR i) then h'(RKRsend@R i,k').
let OCKIsend @system:S (tau:timestamp) =
  fun i => if I i <= tau && (HealthyI i) then h'(RKIsend@I i,k').    


let OCKRreceive @system:S (tau:timestamp) =
  fun i => if R i <= tau && (HealthyR (ind_pred i)) && not (SyncIR (ind_pred i))  then h'(RKRreceive@R i,k').

let OCKIreceive @system:S (tau:timestamp) =
  fun i => if I i <= tau && (HealthyI (ind_pred i)) && not (SyncRI i)  then  h'(RKIreceive@I i,k').

(* We leak `stXSend` whenever we are not trying to prove 
   its secrecy. i.e. when the root key is healthy *)
let ORKRsend @system:S (tau:timestamp) = 
  fun i => if R i <= tau && not (HealthyR i) then RKRsend@R i.
let ORKIsend @system:S (tau:timestamp) = 
  fun i => if I i <= tau && not (HealthyI i) then RKIsend@I i.

(* We leak `stYReceive` only if it is not equal to one of the keys 
   on the sending side (that is, one of the `stXSend`),
   i.e. when not synchronized.
   Rvoiding this duplicate is important to apply the PRF assumption *)
let ORKIreceive @system:S (tau:timestamp) = 
  fun i => if I i <= tau && not (SyncRI i) && not(HealthyI (ind_pred i)) then RKIreceive@I i.
let ORKRreceive @system:S (tau:timestamp) = 
  fun i => if R i <= tau && not (SyncIR (ind_pred i)) && not(HealthyR (ind_pred i) ) then RKRreceive@R i.

   
(* 2) Oracles which do not change throughout the induction. *)

(* DDH oracles, allowed to apply gdh. *)
let OddhR @system:S = fun (y,x:G,i:index) => ( y=x^(skR i) ).
let OddhI @system:S = fun (y,x:G,i:index) => ( y=x^(skI i) ).

(* leak `skI i`, `skR i` as soon as they can be compromised.*)
let OleakRsk @system:S =
  fun (i:index) =>
    if not (safeR i) then 
      skR i 
    else
      zE.
let OleakIsk @system:S =
  fun (i:index) =>
    if not (safeI i) then 
      skI i 
    else
      zE.

(* We define a tuple value that contains all public values
   that does not changes throught the induction.*)
let Opublic = 
 (fun x => h(x,k),
  fun x => h'(x,k'),
  fun i => g^skR i,
  fun i => g^skI i,
  OddhR,
  OddhI,
  OleakRsk,
  OleakIsk,
  h'(RKIsend@init,k')
).

(************************************)
(******** Main Oracle tuples ********)
(************************************)

(* The main tuple of oracles, named `Oracles`, have to be sufficent for the
   attacker to compute the frame, until a given timestamp.
   This tuple is used to prove the secrecy of healthy root keys,
   so it can only access unhealthy (or unsyncronised) root keys and
   chain keys that are derived from healthy root keys.
   `Oracles tau1l tau2l tau3l` has three arguments parameterising different oracles,
   because that reflects the structure of the proof
   (in the induction, we will decrease `tau1l` first, then `tau3l`, etc) *)
let Oracles @system:S (tau1l, tau2l, tau3l, tau4l:timestamp) =
  (OCKRsend tau1l,
   OCKIsend tau1l,
   ORKRsend tau2l,
   ORKIreceive tau3l,
   ORKIsend tau2l,
   ORKRreceive tau3l,
   Opublic,
   OCKRreceive tau4l,
   OCKIreceive tau4l).

(************************************)
(*** Oracles for unsyncronisation ***)
(************************************)

(* These oracles are used only at one proof step:
   to preserve the secret when R is unsync and not (yet) I, or reciprocally.
   In these oracles, we give the attacker any names, except `skR iR` and `skI iI`. *)

let OleakRskExceptiR @system:S (iR:index) = fun (j:index) => if j <> iR then skR j else zE.
let OleakIskExceptiI @system:S (iI:index) = fun (j:index) => if j <> iI then skI j else zE.

let OUnsync @system:S (iR,iI:index) =
  (fun (x:message) => h (x, k),
   fun (x:message) => h' (x, k'),
   fun (i:index) => g ^ skR i,
   fun (i:index) => g ^ skI i,
   OddhR,
   OddhI,
   OleakRskExceptiR iR,
   OleakIskExceptiI iI,
   s_init,
   s_dum).



(********************)
(* Stability lemmas *)
(********************)

(* The oracles are stable by going over pred, unless it is their
   corresponding action. *)

lemma stable_OCKRsend @set:S/left (tau : timestamp [const]):
 (forall i, tau <> R i) => OCKRsend tau = OCKRsend (pred tau).
Proof.
intro Eq.
apply fun_ext.
intro x.
have Eq' := Eq x.
rewrite /OCKRsend /=. 
by fa.  
Qed.

lemma stable_OCKIsend @set:S/left (tau : timestamp [const]):
 (forall i, tau <> I i) => OCKIsend tau = OCKIsend (pred tau).
Proof.
intro Eq.
apply fun_ext.
intro x.
have Eq' := Eq x.
rewrite /OCKIsend /=. 
by fa.  
Qed.

lemma stable_OCKRreceive @set:S/left (tau : timestamp [const]):
 (forall i, tau <> R i) => OCKRreceive tau = OCKRreceive (pred tau).
Proof.
intro Eq.
apply fun_ext.
intro x.
have Eq' := Eq x.
rewrite /OCKRreceive /=. 
by fa.  
Qed.

lemma stable_OCKIreceive @set:S/left (tau : timestamp [const]):
 (forall i, tau <> I i) => OCKIreceive tau = OCKIreceive (pred tau).
Proof.
intro Eq.
apply fun_ext.
intro x.
have Eq' := Eq x.
rewrite /OCKIreceive /=. 
by fa.  
Qed.


lemma stable_ORKRsend @set:S/left (tau : timestamp [const]):
 (forall i, tau <> R i) => ORKRsend tau = ORKRsend (pred tau).
Proof.
intro Eq.
apply fun_ext.
intro x.
have Eq' := Eq x.
rewrite /ORKRsend /=. 
by fa.  
Qed.

lemma stable_ORKIreceive @set:S/left (tau : timestamp [const]):
 (forall i, tau <> I i) => ORKIreceive tau = ORKIreceive (pred tau).
Proof.
intro Eq.
apply fun_ext.
intro x.
have Eq' := Eq x.
rewrite /ORKIreceive /=. 
by fa.  
Qed.

lemma stable_ORKIsend @set:S/left (tau : timestamp [const]):
 (forall i, tau <> I i) => ORKIsend tau = ORKIsend (pred tau).
Proof.
intro Eq.
apply fun_ext.
intro x.
have Eq' := Eq x.
rewrite /ORKIsend /=. 
by fa.  
Qed.

lemma stable_ORKRreceive @set:S/left (tau : timestamp [const]):
 (forall i, tau <> R i) => ORKRreceive tau = ORKRreceive (pred tau).
Proof.
intro Eq.
apply fun_ext.
intro x.
have Eq' := Eq x.
rewrite /ORKRreceive /=. 
by fa.  
Qed.


(********************)
(* Deduction lemmas *)
(********************)

(* When an oracle is not stable by going over pred, we prove
   that we can compute the result of `O tau` with `O (pred tau)`
   and a message `m` used to complete the oracle.
   For instance, `OCKRsend (R i)` gives the same response as
   `OCKRsend (pred(R i))` except on the input `i`.
   So we choose `m` as `(OCKRsend (R i)) i`, i.e. `if HealthyR i then ...`. *)

global lemma OCKRsend_split @set:S/left (i:index [const]) :
[happens(R i)] -> 
  $(        (OCKRsend (pred (R i)),
            if HealthyR i then h'(RKRsend@R(i), k'))
       |>
          (OCKRsend (R i))
       )
.
Proof.
 rewrite /OCKRsend in *.  intro Hap.
      rewrite /( |> ) /=.
       exists 
        (fun (x:_*_) => fun (i0:index) => if i0=i then x#2 else (x#1) i0).
       rewrite /= fun_eq /=.
       intro x. 
       case x=i. 
       ++ intro E.  by rewrite E timestamp_le_refl /=.
       ++ intro NE. simpl. case R x <= R i.
        +++ intro H. by rewrite timestamp_lt_pred. 
        +++ intro H. by rewrite !if_false.
Qed.


global lemma OCKIsend_split @set:S/left (i:index [const]) :
[happens(I i)] -> 
  $(        (OCKIsend (pred (I i)),
            if HealthyI i then h'(RKIsend@I(i), k'))
       |>
          (OCKIsend (I i))
       )
.
Proof.
 rewrite /OCKIsend in *.  intro Hap.
      rewrite /( |> ) /=.
       exists 
        (fun (x:_*_) => fun (i0:index) => if i0=i then x#2 else (x#1) i0).
       rewrite /= fun_eq /=.
       intro x. 
       case x=i. 
       ++ intro E.  by rewrite E timestamp_le_refl /=.
       ++ intro NE. simpl. case I x <= I i.
        +++ intro H. by rewrite timestamp_lt_pred. 
        +++ intro H. by rewrite !if_false.
Qed.


global lemma OCKRreceive_split @set:S/left (i:index [const]) :
[happens(R i)] -> 
  $(        (OCKRreceive (pred (R i)),
            if HealthyR (ind_pred i) &&  not (SyncIR (ind_pred i)) then h'(RKRreceive@R(i), k'))
       |>
          (OCKRreceive (R i))
       )
.
Proof.
 rewrite /OCKRreceive in *.  intro Hap.
      rewrite /( |> ) /=.
       exists 
        (fun (x:_*_) => fun (i0:index) => if i0=i then x#2 else (x#1) i0).
       rewrite /= fun_eq /=.
       intro x. 
       case x=i. 
       ++ intro E.  by rewrite E timestamp_le_refl /=.
       ++ intro NE. simpl. case R x <= R i.
        +++ intro H. by rewrite timestamp_lt_pred. 
        +++ intro H. by rewrite !if_false.
Qed.


global lemma OCKIreceive_split @set:S/left (i:index [const]) :
[happens(I i)] -> 
  $(        (OCKIreceive (pred (I i)),
            if HealthyI (ind_pred i) && not (SyncRI i) then h'(RKIreceive@I(i), k'))
       |>
          (OCKIreceive (I i))
       )
.
Proof.
 rewrite /OCKIreceive in *.  intro Hap.
      rewrite /( |> ) /=.
       exists 
        (fun (x:_*_) => fun (i0:index) => if i0=i then x#2 else (x#1) i0).
       rewrite /= fun_eq /=.
       intro x. 
       case x=i. 
       ++ intro E.  by rewrite E timestamp_le_refl /=.
       ++ intro NE. simpl. case I x <= I i.
        +++ intro H. by rewrite timestamp_lt_pred. 
        +++ intro H. by rewrite !if_false.
Qed.

global lemma ORKRsend_split @set:S/left (i:index [const]) :
[happens(R i)] -> 
  $(        (ORKRsend (pred (R i)),
            if not (HealthyR i) then RKRsend@R(i))
       |>
            (ORKRsend (R i))
       ).
Proof.
 rewrite /ORKRsend in *.  intro Hap.
 rewrite /( |> ) /=.
       exists 
        (fun (x:_*_) => fun (i0:index) => if i0=i then x#2 else (x#1) i0).
       rewrite /= fun_eq /=.
       intro x. 
       case x=i. 
       ++ intro E. by rewrite E timestamp_le_refl /=.
       ++ intro NE. simpl. case R x <= R i.
        +++ intro H. by rewrite timestamp_lt_pred. 
        +++ intro H. by rewrite !if_false.
Qed.

global lemma ORKRreceive_split @set:S/left (i:index [const]) :
[happens(R i)] -> 
  $(        (ORKRreceive (pred (R i)),
            if not (SyncIR (ind_pred i)) && not(HealthyR (ind_pred i)) then RKRreceive@R(i))
       |>
            (ORKRreceive (R i))
       ).
Proof.
 rewrite /ORKRreceive in *.  intro Hap.
 rewrite /( |> ) /=.
       exists 
        (fun (x:_*_) => fun (i0:index) => if i0=i then x#2 else (x#1) i0).
       rewrite /= fun_eq /=.
       intro x. 
       case x=i. 
       ++ intro E. by rewrite E timestamp_le_refl /=.
       ++ intro NE. simpl. case R x <= R i.
        +++ intro H. by rewrite timestamp_lt_pred. 
        +++ intro H. by rewrite !if_false.
Qed.


global lemma ORKIsend_split @set:S/left (i:index [const]) :
[happens(I i)] -> 
  $(        (ORKIsend (pred (I i)),
            if not (HealthyI i) then RKIsend@I(i))
       |>
            (ORKIsend (I i))
       ).
Proof.
 rewrite /ORKIsend in *.  intro Hap.
 rewrite /( |> ) /=.
       exists 
        (fun (x:_*_) => fun (i0:index) => if i0=i then x#2 else (x#1) i0).
       rewrite /= fun_eq /=.
       intro x. 
       case x=i. 
       ++ intro E. by rewrite E timestamp_le_refl /=.
       ++ intro NE. simpl. case I x <= I i.
        +++ intro H. by rewrite timestamp_lt_pred. 
        +++ intro H. by rewrite !if_false.
Qed.

global lemma ORKIreceive_split @set:S/left (i:index [const]) :
[happens(I i)] -> 
  $(        (ORKIreceive (pred (I i)),
            if not (SyncRI (i)) && not(HealthyI (ind_pred i)) then RKIreceive@I(i))
       |>
            (ORKIreceive (I i))
       ).
Proof.
 rewrite /ORKIreceive in *.  intro Hap.
 rewrite /( |> ) /=.
       exists 
        (fun (x:_*_) => fun (i0:index) => if i0=i then x#2 else (x#1) i0).
       rewrite /= fun_eq /=.
       intro x. 
       case x=i. 
       ++ intro E. by rewrite E timestamp_le_refl /=.
       ++ intro NE. simpl. case I x <= I i.
        +++ intro H. by rewrite timestamp_lt_pred. 
        +++ intro H. by rewrite !if_false.
Qed.



(*****************)
(* Specification *)
(*****************)

(* We prove here that under the correct condition,
   the oracles can return some values. *)

global lemma ORKRsend_pred  @set:S/left :
 Forall (j:index [const]), [happens(R j)] -> 
	[not (HealthyR (ind_pred j))] -> 
	 $(  (ORKRsend (pred (R(j)))) |>  (RKRsend@pred (R(j) ) )). 
Proof.
intro j Hap NH.
rewrite RKRsend_pred => //.


ghave [H|H] : [j=ind_one || j<> ind_one] by auto.
+ rewrite -healthyR_to_HealthyR /healthyR in NH. 
  rewrite or_true_left in NH => //.
  by rewrite H.   
+ rewrite if_false => //.

rewrite /ORKRsend.
rewrite /( |>).
exists (fun x => x (ind_pred j)).

rewrite if_true /=.  
by smt.
by simpl.
Qed.



global lemma ORKRsend_ded  @set:S/left :
 Forall (j:index [const]), [happens(R j)]-> [not (HealthyR j)] ->  $(  (ORKRsend ((R(j)))) |>  (RKRsend@(R(j) ) )). 
Proof.


intro j Hap NH.

rewrite /ORKRsend.
rewrite /( |>).
exists (fun x => x (j)).

rewrite if_true.
auto.  
auto.
Qed.



global lemma ORKIsend_pred  @set:S/left :
 Forall (j:index [const]), [happens(I j)] -> 
	[not (HealthyI (ind_pred j))] -> 
	 $(  (ORKIsend (pred (I(j)))) |>  (RKIsend@pred (I(j) ) )). 
Proof.
intro j Hap NH.
rewrite RKIsend_pred => //.


ghave [H|H] : [j=ind_one || j<> ind_one] by auto.
+ rewrite -healthyI_to_HealthyI healthyI_zero  in NH. 
  by rewrite H. 
  by simpl.

+ rewrite if_false => //.

rewrite /ORKIsend.
rewrite /( |>).
exists (fun x => x (ind_pred j)).

rewrite if_true /=.  
by smt.
by simpl.
Qed.



(******************)
(* Bigger oracles *)
(******************)

(* Here we prove that an oracle `O tau'` is deducible
   from `O tau` if `tau' < tau` *)

global lemma bigger_O @set:S/left :
  Forall (act : index -> timestamp[const])
         (condition : index -> boolean[const])
         (result : index -> message)
         (tau,tau':timestamp [const]),
    [tau' <= tau] ->
    $( (fun i => if act i <= tau  && condition i then result i)
    |> (fun i => if act i <= tau' && condition i then result i) ).
Proof.
  intro act condition result tau tau' Ord.
  rewrite /( |> ). 
  exists (fun x => (fun (i:index) =>
    if (act i <= tau' && condition i) then x i)).
  simpl.
  apply fun_ext.
  intro i.
  simpl.
  by rewrite (if_true (act i <= tau && _)).
Qed.
 
global lemma bigger_ORKRreceive @set:S/left :
 Forall (tau,tau':timestamp [const]),
   [tau' <= tau] -> 
   $( (ORKRreceive tau ) |> (ORKRreceive tau') ). 
Proof.
  by have H := bigger_O
    (fun i => R i)
    (fun i => not(SyncIR (ind_pred i))&& not(HealthyR (ind_pred i)))
    (fun i => RKRreceive@R i).
Qed.

global lemma bigger_ORKIreceive @set:S/left :
 Forall (tau,tau':timestamp [const]),
   [tau' <= tau] -> 
   $( (ORKIreceive tau ) |> (ORKIreceive tau') ). 
Proof.
  by have H := bigger_O
    (fun i => I i)
    (fun i => not(SyncRI i) && not(HealthyI (ind_pred i)))
    (fun i => RKIreceive@I i).
Qed.

global lemma bigger_OhRS @set:S/left :
 Forall (tau,tau':timestamp [const]),
   [tau' <= tau] -> 
   $( (OCKRsend tau ) |> (OCKRsend tau') ). 
Proof.
  by have H := bigger_O
    (fun i => R i)
    HealthyR
    (fun i => h'(RKRsend@R i, k')).
Qed.

global lemma bigger_OhIS @set:S/left :
 Forall (tau,tau':timestamp [const]),
   [tau' <= tau] -> 
   $( (OCKIsend tau ) |> (OCKIsend tau') ). 
Proof.
  by have H := bigger_O
    (fun i => I i)
    HealthyI
    (fun i => h'(RKIsend@I i, k')).
Qed.


global lemma bigger_OhRR @set:S/left :
 Forall (tau,tau':timestamp [const]),
   [tau' <= tau] -> 
   $( (OCKRreceive tau ) |> (OCKRreceive tau') ). 
Proof.
  by have H := bigger_O
    (fun i => R i)
    (fun i => HealthyR (ind_pred i) && not(SyncIR (ind_pred i)))
    (fun i => h'(RKRreceive@R i, k')).
Qed.

global lemma bigger_OhIR @set:S/left :
 Forall (tau,tau':timestamp [const]),
   [tau' <= tau] -> 
   $( (OCKIreceive tau ) |> (OCKIreceive tau') ). 
Proof.
  by have H := bigger_O
    (fun i => I i)
    (fun i => HealthyI (ind_pred i) && not(SyncRI i))
    (fun i => h'(RKIreceive@I i, k')).
Qed.


global lemma bigger_ORKRsend @set:S/left :
 Forall (tau,tau':timestamp [const]),
   [tau' <= tau] -> 
   $( (ORKRsend tau ) |> (ORKRsend tau') ). 
Proof.
  by have H := bigger_O
    (fun i => R i)
    (fun i => not (HealthyR i))
    (fun i => RKRsend@R i).
Qed.

global lemma bigger_ORKIsend @set:S/left :
 Forall (tau,tau':timestamp [const]),
   [tau' <= tau] -> 
   $( (ORKIsend tau ) |> (ORKIsend tau') ). 
Proof.
  by have H := bigger_O
    (fun i => I i)
    (fun i => not (HealthyI i))
    (fun i => RKIsend@I i).
Qed.

(* for all oracles at once *)
global lemma bigger_Oracles @set:S/left 
 (tau1l, tau1l', tau2l, tau2l', tau3l, tau3l', tau4l, tau4l':timestamp[const]) :
  [tau1l' <= tau1l] ->
  [tau2l' <= tau2l] ->
  [tau3l' <= tau3l] ->
  [tau4l' <= tau4l] ->
  $( (Oracles tau1l tau2l tau3l tau4l) |> (Oracles tau1l' tau2l' tau3l' tau4l') ).
Proof.
 intro Htau1 Htau2 Htau3 Htau4.
 rewrite /Oracles. 
 deduce with (bigger_OhRS tau1l tau1l'); [1:auto].
 deduce with (bigger_OhIS tau1l tau1l'); [1:auto].
 deduce with (bigger_OhRR tau4l tau4l'); [1:auto].
 deduce with (bigger_OhIR tau4l tau4l'); [1:auto].
 deduce with (bigger_ORKRsend tau2l tau2l'); [1:auto].
 deduce with (bigger_ORKIsend tau2l tau2l'); [1:auto].
 deduce with (bigger_ORKRreceive tau3l tau3l'); [1:auto].
 deduce with (bigger_ORKIreceive tau3l tau3l'); [1:auto].
Qed.



lemma [S/left] expand_rhs side taur n n2:
happens(taur) =>
(if (side = 4) then RKRsend@taur
else if (side = 3) then RKIsend@taur
else if (side = 2) then RKRreceive@taur
else if (side = 1) then RKIreceive@taur
else if (side = 0) then ofG(g^(skR n ** skI (n2)))
)
= 
if (side = 4) then
  try find j:index such that (taur = R(j))
  in
    h
      (<h (<RKRsend@pred (R(j)),ofG (gRecR@R(j))>, k),ofG (gSendR@R(j))>,
       k)
  else (if (taur = init) then s_init else RKRsend@pred taur)

else if (side = 3) then
  try find j:index such that (taur = I(j))
  in
    h
      (<h (<RKIsend@pred (I(j)),ofG (gRecI@I(j))>, k),ofG (gSendI@I(j))>,
       k)
  else (if (taur = init) then RKIsend@init else RKIsend@pred taur)

else if (side = 2) then
  try find j:index such that (taur = R(j))
  in h (<RKRsend@pred (R(j)),ofG (gRecR@R(j))>, k)
  else (if (taur = init) then RKRreceive@init else RKRreceive@pred taur)

else if (side = 1) then
  try find j:index such that (taur = I(j))
  in h (<RKIsend@pred (I(j)),ofG (gRecI@I(j))>, k)
  else
    (if (taur = init) then s_init     else RKIreceive@pred taur)
else if (side = 0) then ofG(g^(skR n ** skI (n2)))

.
Proof.
intro Hap.
have stIR :
 RKIreceive@taur  =
  try find j such that taur = I j in 
    h (<RKIsend@pred (I(j)), ofG (gRecI@I(j))>, k)
  else
    (if taur = init then s_init else RKIreceive@pred(taur)).
{
 simpl.
 rewrite try_carac_1.
 case taur; 
 try ( rewrite if_false => //;
       by constraints + by rewrite if_false => //).
 intro [j Eq].
 rewrite if_true.   by exists j. simpl.
 rewrite Eq  /RKIreceive.
 rewrite (choose_uniq j) => //.    
}.

ghave stRR :
 [RKRreceive@taur  =
  try find j such that taur = R j in 
    h (<RKRsend@pred (R(j)),ofG (gRecR@R(j))>, k)
  else
    (if taur = init then RKRreceive@init else RKRreceive@pred(taur))].
 {
 simpl.
 rewrite try_carac_1.
 case taur; 
 try ( rewrite if_false => //; 
       by constraints + by rewrite if_false => //).
 intro [j Eq].
 rewrite if_true.   by exists j. simpl.
 rewrite Eq /RKRreceive.
 rewrite (choose_uniq j) => //.     
}.

ghave stR :
   [RKRsend@taur  =
    try find j such that taur = R j in 
      h(<h (<RKRsend@pred (R(j)),ofG (gRecR@R(j))>, k), 
         ofG(gSendR@R(j))>, k)
    else
      (if taur = init then s_init else RKRsend@pred(taur))].
 {
 simpl.
 rewrite try_carac_1.
 case taur; 
 try ( rewrite if_false => //; 
       by constraints + by rewrite if_false => //).
 intro [j Eq].
 rewrite if_true.   by exists j. simpl.
 rewrite Eq /RKRsend /RKRreceive.
 rewrite (choose_uniq j) => //.     
}.
     
ghave stI :
  [RKIsend@taur  =
   try find j such that taur = I j in 
     h(<h (<RKIsend@pred (I(j)), ofG (gRecI@I(j))>, k),
       ofG(gSendI@I(j))>, k)
   else
     (if taur = init then RKIsend@init else RKIsend@pred(taur))].
 {
  simpl.
  rewrite try_carac_1.
  case taur; 
  try ( rewrite if_false => //;
        by constraints + by rewrite if_false => //).
  intro [j Eq].
  rewrite if_true.   by exists j. simpl.
  rewrite Eq /RKIsend /RKIreceive.
  rewrite (choose_uniq j) => //.    
 }.

rewrite stIR stRR stR stI.
fa => ?. {
  fa => //=.
  smt ~no_macros.
}.
fa => ?.
+ fa => // ?. 
+ fa => //=.
  smt ~no_macros.
Qed.



lemma [S/left] expand_ORKIsend i:
          ORKIsend (I i) = 
            (fun (i0:index) =>
                 if (I(i0) <= I(i) && not (HealthyI i0)) then
                   (if happens(I(i0)) then
                h
                  (<h (<RKIsend@pred (I(i0)),ofG (gRecI@I(i0))>, k),
                 ofG (gSendI@I(i0))>,
                    k)
                else witness)).
Proof.
rewrite /ORKIsend.
smt.
Qed.
         
lemma [S/left] expand_ORKIreceive i:
  ORKIreceive (I i) =
           fun (j:index) =>
             if (I(j) <= I i && not (SyncRI j)) && not(HealthyI (ind_pred j)) then
              (if happens(I(j)) then  h (<RKIsend@pred (I(j)),ofG (gRecI@I(j))>, k)).
Proof.
rewrite /ORKIreceive.
expand ~def RKIreceive. 
smt ~no_macros.
Qed.    

lemma [S/left] expand_ORKRreceive i:
          ORKRreceive (R i) = 
           fun (i':index) =>
             if (R(i') <= R i && not (SyncIR (ind_pred i'))) && not(HealthyR (ind_pred i')) then
              (if happens(R(i')) then 
                    h (<RKRsend@pred (R(i')),ofG (gRecR@R(i'))>, k)
               else witness).
Proof.
          rewrite /ORKRreceive.
           expand ~def RKRreceive. smt ~no_macros.
Qed.

lemma [S/left] expand_ORKRsend i :
          ORKRsend (R i) = 
            (fun (i0:index) =>
                 if (R(i0) <= R(i) && not (HealthyR i0)) then
                   (if happens(R(i0)) then
                h
                  (<h (<RKRsend@pred (R(i0)),ofG (gRecR@R(i0))>, k),
                 ofG (gSendR@R(i0))>,
                    k)
                else witness)).
Proof.
          rewrite /ORKRsend /RKRsend /RKRreceive. smt.
Qed.

lemma [S/left] expand_OCKRreceive i:
         OCKRreceive (R i) = 
            fun (i0:index) =>
               if (R(i0) <= R(i) && HealthyR (ind_pred i0) && not (SyncIR (ind_pred i0))) then
                h' (h (<RKRsend@pred (R(i0)),ofG (gRecR@R(i0))>, k), k').
Proof.
          rewrite /OCKRreceive.
           expand ~def RKRreceive. smt ~no_macros.
Qed.


lemma [S/left] expand_OCKIreceive i: 
         OCKIreceive (I i) = 
            fun (i0:index) =>
	       if (I(i0) <= I(i) && HealthyI (ind_pred i0) && not (SyncRI i0)) then
                h' (h (<RKIsend@pred (I(i0)),ofG (gRecI@I(i0))>, k), k').
Proof.
          rewrite /OCKIreceive.
           expand ~def RKIreceive. smt ~no_macros.
Qed.


