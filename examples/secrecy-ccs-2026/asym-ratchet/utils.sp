(* This file defines small lemmas useful for some rewriting in some
   specific proofs *)

include Core.
include NonDeduction.
include[admit] "model.sp".

(* ------------------------------ *)

(* Lemmas on pairs. Consequence of the axiom `proj_inj` *)
lemma[any] pair_eq (x,y,z:message) : (x = <y,z>) = (fst x = y && snd x = z).
Proof.
  rewrite eq_iff; split.
  + auto.
  + intro _. by apply proj_inj.
Qed.

(* ------------------------------ *)

(* Useful lemmas to quickly rewrite HealthyR and SyncRI. *)
lemma [any] or_false_left (x,y:bool) :
  not(x) => (x || y) = y.
Proof.
  intro H.
  rewrite -not_eqfalse in H.
  by rewrite H or_false_l.
Qed.

lemma [any] or_false_right (x,y:bool) :
  not(y) => (x || y) = x.
Proof.
  intro H.
  rewrite -not_eqfalse in H.
  by rewrite H or_false_r.
Qed.

lemma [any] or_true_left (x,y:bool) :
  x => (x || y) = true.
Proof.
  intro H.
  rewrite -eq_true in H.
  by rewrite H or_true_l.
Qed.

lemma [any] or_true_right (x,y:bool) :
  y => (x || y) = true.
Proof.
  intro H.
  rewrite -eq_true in H.
  by rewrite H or_true_r.
Qed.

(* ------------------------------ *)

(* Lemmas to quickly simplify some calls to the `choose` operator *)
lemma [any] choose_uniq ['a] (x:'a,phi: 'a -> bool) :
  (phi x) => ( forall y, x<>y => not(phi y)) => choose (phi) = x.
Proof.
  search choose.
  intro H1 H2.
  apply choose_spec in H1.
  by have H3 := H2 (choose phi).
Qed.

lemma simpl_chooseR @system:S : forall j,
  happens(R j) => choose(fun i => R i = R j) = j.
Proof.
  intro j Hap.
  by apply choose_uniq.
Qed.

lemma simpl_chooseI @system:S : forall j,
  happens(I j) => choose(fun i => I i = I j) = j.
Proof.
  intro j Hap.
  by apply choose_uniq.
Qed.

(* ------------------------------ *)

lemma [any] fun_eq ['a 'b]  (f,g : 'a -> 'b):
 (f =g) = (forall x:'a, f x = g x).
Proof.
 rewrite eq_iff.
 split.
  - auto.
  - by apply fun_ext.
Qed.  

exact lemma [any] timestamp_le_refl (tau:timestamp) :
  happens(tau) => ((tau <= tau) = true).
Proof.
  auto.
Qed.

exact lemma [any] timestamp_le_init (t:timestamp) :
  (t <= init) = (t = init).
Proof.
  by rewrite eq_iff. 
Qed.

exact lemma [any] timestamp_le_pred (t:timestamp) :
  (t <= pred t) = false.
Proof.
  by rewrite eq_iff. 
Qed.

exact lemma [any] timestamp_lt_pred (t,t':timestamp) :
  t < t' => (t <= pred t') = true.
Proof.
  by rewrite eq_iff. 
Qed.

exact lemma [any] timestamp_pred_lt (t:timestamp) :
  happens(t) => t <> init => (pred t < t) = true.
Proof.
  auto.
Qed.
hint rewrite timestamp_le_refl.
hint rewrite timestamp_le_init.
hint rewrite timestamp_le_pred.
hint rewrite timestamp_lt_pred.
hint rewrite timestamp_pred_lt.


(***********************)
(* Deduction utilities *)
(***********************)

global lemma
  no_ded_ded @set:S/left ['a 'b 'c]  (u : 'a) (v : 'b) (w : 'c) : 
    $(u *> w) ->
    $(u |> v) ->
    $(v *> w).
Proof.
   intro @/( |> ) @/( *> ) H1 [f H2] g.
   have R /= := H1 (fun x => g(f x)).
  auto.
Qed.


global lemma
  if_true_ded @set:S/left ['a 'b]  (b : bool) (u : 'a) (v : 'b) (w : 'b) : 
    $(u *> (if b then v else w))  ->
    [b] -> 
    $(u *> v) .
Proof.
   intro Nded I.
   rewrite if_true in Nded. by auto. by assumption.
Qed.

global lemma
  if_false_ded @set:S/left ['a 'b]  (b : bool) (u : 'a) (v : 'b) (w : 'b) : 
    $(u *> (if b then v else w))  ->
    [not b] -> 
    $(u *> w) .
Proof.
   intro Nded I.
   rewrite if_false in Nded. by auto. by assumption.
Qed.


global lemma ded_f @set:S/left (f:message -> message)  (v:message) :
$(  ( fun (m:message) =>  f m,  v) |> (f v) ).
Proof.
rewrite /( |>).
by exists (fun x : _*_ => ((x#1) (x#2))).
Qed.

global lemma ded_right @set:S/left ['a]
  (g:message -> message [adv]) (v:message) (u:'a) :
  $(u *> (g v)) -> $(u *> v).
Proof.
 rewrite /( *>).
 intro Neg f.
 by have _ := Neg (fun x => g (f x)).
Qed.


(******* Pairs *******)
(* Used to designate a step in the hashes chains *)
(* (0, false) < (0, true) < (1, false) < ... *)

let pair_init @system:S = (ind_zero, false).

exact axiom pair_order @system:S : forall (p, p' : index * bool),
  (p < p') = ((p#1) ~< (p'#1) || (p#1 = p'#1 && not (p#2) && (p'#2))).

let pair_pred @system:S (p : index * bool) =
  if p#2 then
    (p#1, false)
  else
    (ind_pred (p#1), true).

(* Lemmas on pair order *)
lemma pair_order_min @system:S : forall p, not (p < pair_init).
Proof.
  intro p F.
  have H := pair_order p pair_init.
  rewrite /pair_init /= in *.
  smt ~no_macros.
Qed.

lemma pair_order_tricho @system:S : 
     forall (p, p' : index * bool), p = p' || p < p' || p' < p.
Proof.
  intro p p'.
  rewrite pair_order pair_order /=.
  smt ~no_macros.
Qed.

lemma pair_order_pred1 @system:S : forall (p : index * bool),
  p <> pair_init => pair_pred p < p.
Proof.
  intro p.
  rewrite /pair_init /pair_pred pair_order /=.
  smt ~no_macros.
Qed.

lemma pair_order_pred2 @system:S : forall (p, p' : index * bool),
  p <> pair_init => p < p' => pair_pred p < pair_pred p'.
Proof.
  intro p p'.
  rewrite /pair_init /pair_pred !pair_order /=.
  smt ~no_macros.
Qed.

lemma pair_order_pred3 @system:S : forall (p, p' : index * bool),
  p < p' => p <= pair_pred p'.
Proof.
  intro p p' H.
  search _ <= _.
  case (p = pair_pred p'); intro C.
  - rewrite C.
    apply eq_impl_le.
  - apply lt_impl_le.
    rewrite /pair_pred pair_order in *.
    case H; 2: smt ~no_macros.
    case (p'#2); intro C2.
    + auto.
    + simpl.
      smt ~no_macros.
Qed.
