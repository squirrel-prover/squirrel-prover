set autoIntro = false.

hash H.
hash G.
name k : message.
name k' : message.
name s0 : message.
mutable s : message = s0.

channel o.
channel c.

system (
   (O: !_i in(o,x); out(o,<H(x,k),G(x,k')>)) |
   (A: !_i s:=H(s,k); out(o,G(s,k')))
).



(* LIBRAIRIES *)

axiom eq_iff (x, y : boolean) : (x = y) = (x <=> y).

goal eq_refl ['a] (x : 'a) : (x = x) = true. 
Proof. print.
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl.

goal eq_sym ['a] (x,y : 'a) : x = y => y = x.
Proof. auto. Qed.

(* SP: merge with eq_refl *)
goal eq_refl_i (x : index) : (x = x) = true.
Proof.
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl_i.

(* SP: merge with eq_refl *)
goal eq_refl_t (x : timestamp) : (x = x) = true.
Proof.
  by rewrite eq_iff. 
Qed.
hint rewrite eq_refl_t.


axiom not_true : not(true) = false.
hint rewrite not_true.

axiom not_false : not(false) = true.
hint rewrite not_false.

(* new *)
axiom true_false : (true = false) = false.
hint rewrite true_false.

(* new *)
goal false_true : (false = true) = false.
Proof. 
  (* TODO: work-around until we have a better type inference *)
  (* rewrite (eq_sym false true). *)
  assert (forall (x,y : boolean), (x = y) = (y = x)) as H .
    intro _ _. 
    by rewrite eq_iff. 
  rewrite (H false true).
  auto.
Qed.
hint rewrite false_true.

goal not_not (b : boolean): not (not b) = b. 
Proof.
  by case b.
Qed.
hint rewrite not_not.

goal not_eq ['a] (x, y : 'a): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq.

(* new *)
goal not_eq_i (x, y : index): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq_i.

(* new *)
goal not_eq_t (x, y : timestamp): not (x = y) = (x <> y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_eq_t.

goal not_neq ['a] (x, y : 'a): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq.

(* new *)
goal not_neq_i (x, y : index): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq_i.

(* new *)
goal not_neq_t (x, y : timestamp): not (x <> y) = (x = y).
Proof. 
by rewrite eq_iff. 
Qed.
hint rewrite not_neq_t.

(* new *)
goal eq_false ['a] (x, y : 'a): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false.

(* new *)
goal eq_false_i (x, y : index): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq_i. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false_i.

(* new *)
goal eq_false_t (x, y : timestamp): ((x = y) = false) = (x <> y).
Proof. 
rewrite -not_eq_t. case (x = y) => _. simpl. auto.
by rewrite eq_iff. 
Qed.
hint rewrite eq_false_t.


(*------------------------------------------------------------------*)
(* and *)
axiom and_comm (b,b' : boolean) : (b && b') = (b' && b).

axiom and_true_l (b : boolean) : (true && b) = b.
hint rewrite and_true_l.

goal and_true_r (b : boolean) : (b && true) = b.
Proof. by rewrite and_comm and_true_l. Qed.
hint rewrite and_true_r.

axiom and_false_l (b : boolean) : (false && b) = false.
hint rewrite and_false_l.

goal and_false_r (b : boolean) : (b && false) = false.
Proof. by rewrite and_comm and_false_l. Qed.
hint rewrite and_false_r.

(*------------------------------------------------------------------*)
(* or *)
axiom or_comm (b,b' : boolean) : (b || b') = (b' || b).

axiom or_false_l (b : boolean) : (false || b) = b.
hint rewrite or_false_l.

goal or_false_r (b : boolean) : (b || false) = b.
Proof. by rewrite or_comm or_false_l. Qed.
hint rewrite or_false_r.

axiom or_true_l (b : boolean) : (true || b) = true.
hint rewrite or_true_l.

goal or_true_r (b : boolean) : (b || true) = true.
Proof. by rewrite or_comm or_true_l. Qed.
hint rewrite or_true_r.

(*------------------------------------------------------------------*)
(* if *)


goal if_true ['a] (b : boolean, x,y : 'a):
 b => if b then x else y = x.
Proof.
  by intro *; yesif.
Qed.

goal if_true0 ['a] (x,y : 'a):
 if true then x else y = x.
Proof.
  by rewrite if_true. 
Qed.
hint rewrite if_true0.

goal if_false ['a] (b : boolean, x,y : 'a):
 (not b) => if b then x else y = y.
Proof.
  by intro *; noif.
Qed.

goal if_false0 ['a] (x,y : 'a):
 if false then x else y = y.
Proof.
  by rewrite if_false.
Qed.
hint rewrite if_false0.

goal if_then_then ['a] (b,b' : boolean, x,y : 'a):
  if b then (if b' then x else y) else y = if (b && b') then x else y.
Proof.  
  by case b; case b'.
Qed.

goal if_same ['a] (b : boolean, x : 'a):
  if b then x else x = x.
Proof.
  by case b.
Qed.
hint rewrite if_same.

(* new *)
goal if_then ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then (if b' then x else y) else z = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then.

(* new *)
goal if_else ['a] (b,b' : boolean, x,y,z : 'a):
 b = b' => 
 if b then x else (if b' then y else z) = 
 if b then x else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_else.

(* new *)
goal if_then_not ['a] (b,b' : boolean, x,y,z : 'a):
 b = not b' => 
 if b then (if b' then x else y) else z = 
 if b then y else z.
Proof.
  by intro ->; case b'.
Qed.
hint rewrite if_then_not.

(* new *)
goal if_else_not ['a] (b,b' : boolean, x,y,z : 'a):
  b = not b' => 
 if b then x else (if b' then y else z) = 
 if b then x else y.
Proof.  
  by intro ->; case b'.
Qed.
hint rewrite if_else_not.

(*------------------------------------------------------------------*)
(* new *)

goal fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.
hint rewrite fst_pair.

goal snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.
hint rewrite snd_pair.

goal diff_eq ['a] (x,y : 'a) : x = y => diff(x,y) = x.
Proof. by project. Qed.
hint rewrite diff_eq.

goal diff_diff_l ['a] (x,y,z: 'a): diff(diff(x,y),z) = diff(x,z).
Proof. by project. Qed.
hint rewrite diff_diff_l.

goal diff_diff_r ['a] (x,y,z: 'a): diff(x,diff(y,z)) = diff(x,z).
Proof. by project. Qed.
hint rewrite diff_diff_r.

goal len_diff (x, y : message) : len(diff(x,y)) = diff(len(x), len(y)).
Proof. by project. Qed.

(*------------------------------------------------------------------*)

(* Others *)

goal le_pred_lt (t, t' : timestamp): (t <= pred(t')) = (t < t').
Proof. 
  by rewrite eq_iff.
Qed.

goal le_not_lt (t, t' : timestamp): 
  t <= t' => not (t < t') => t = t'.
Proof.
  by case t' = init. 
Qed.

goal le_not_lt_charac (t, t' : timestamp):
 (not (t < t') && t <= t') = (happens(t) && t = t').
Proof.
 by rewrite eq_iff.
Qed.

goal lt_impl_le (t, t' : timestamp): 
  t < t' => t <= t'.
Proof. auto. Qed.

goal le_lt (t, t' : timestamp): 
  t <> t' => (t <= t') = (t < t').
Proof. 
  by intro *; rewrite eq_iff. 
Qed.


(* PROOF *)
(** Last update lemmas: basic reasoning about the memory cell.
  * Here we decompose the usual lastupdate lemma to separate the "pure" part
  * from the part that involves message equalities. *)

goal lastupdate_pure : forall tau:timestamp, 
  happens(tau) => (
    (forall j:index, happens(A(j)) => A(j)>tau) ||
    (exists i:index, happens(A(i)) && A(i) <=tau && 
     forall j:index, happens(A(j)) && A(j)<=tau => A(j)<=A(i))).
Proof.
induction.
intro tau IH Hp.
case tau.

(* init *)
intro Eq; left; intro j Hpj; by auto.

(* O(i) *)
intro [i Eq]; subst tau, O(i); use IH with pred(O(i)) => //.
destruct H as [H1 | [i0 H2]].
left; intro j Hpj; by use H1 with j => //.
right; exists i0; repeat split =>//.
destruct H2 as [H21 H22 H23].
intro j [Hpj Ord].
case (A(j) <= pred( O(i))) => //.
use H23 with j => //.

(* A(i) *)
intro [i Eq]; subst tau, A(i); use IH with pred(A(i)) => //.
destruct H as [H1 | [i0 H2]];
try (right;
exists i;
repeat split => //).
Qed.


goal lastupdate_init :
  forall tau:timestamp, 
  happens(tau) => 
  (forall j:index, happens(A(j)) => A(j)>tau) => 
  s@tau = s@init.
Proof.
  induction => tau IH _ Htau.
  case tau.

  auto.

  intro [i Hi]; rewrite Hi in *; expand s@O(i).
  apply IH => //.
  intro j Hp; by use Htau with j.

  intro [i Hi]; rewrite Hi in *.
  by use Htau with i.
Qed.

goal lastupdate_A :
  forall (tau:timestamp,i:index),
  happens(A(i)) && A(i)<=tau && 
  (forall j:index, happens(A(j)) && A(j)<=tau => A(j)<=A(i)) =>
  s@tau = s@A(i).
Proof.
  induction.
  intro tau IH i [Hap Hinf Hsup].

  case tau.

  intro H; rewrite H in Hinf; auto.

  intro [j Hj]; rewrite Hj in *; expand s@O(j).
  apply IH => //; simpl.
  intro k Hk; by use Hsup with k.

  intro [j Hj]; rewrite Hj in *.
  assert i=j; [2: auto | 1: by use Hsup with j].
Qed.

goal lastupdate : 
  forall tau:timestamp, 
  happens(tau) =>
    (s@tau = s@init && forall j:index, happens(A(j)) => A(j)>tau) ||
    (exists i:index, s@tau = s@A(i) && 
     happens(A(i)) && A(i)<=tau && 
     forall j:index, happens(A(j)) && A(j)<=tau => A(j)<=A(i)).
Proof.
  intro tau Htau.
  use lastupdate_pure with tau as [Hinit|[i HAi]] => //.
  left.
  split => //.
  by apply lastupdate_init.
  right; exists i; repeat split => //; by apply lastupdate_A.
Qed.


(** The contents of the memory cell never repeats. *)

goal non_repeating :
  forall (beta,alpha:timestamp) happens(beta) =>
  (exists i:index, alpha < A(i) && A(i) <= beta) =>
  s@alpha <> s@beta.
Proof.
  induction => beta IH alpha _ [i [_ _]] Meq.
  use lastupdate with beta as [[_ Habs] | [j [[_ _] Hsup]]] => //;
    1: by use Habs with i.

  use Hsup with i => //.
  (* We now have alpha < A(i) <= A(j) < beta
   * and no A(_) between A(j) and beta. *)

  assert s@alpha = s@A(j) as Meuf => //; expand s@A(j); euf Meuf => Heuf.

  use IH with pred(A(j)),pred(A(i0)) => //.
  by case Heuf; exists i0.
Qed.

(*
goal charac :
forall (i: index, tau': timestamp) (happens(O(i)) && happens(tau')) =>
( condA  = condB )
).
Proof.
intro i tau' Hap.
rewrite eq_iff; split.

(* => case *)
intro H.

(* <= case *)

Qed.
*)


(** Strong secrecy *)

(* axiom unique_queries : forall (i,j:index) i <> j => input@O(i) <> input@O(j). *)

name m : message.

global goal [default/left,default/left]
  strong_secrecy (tau:timestamp) : forall (tau':timestamp),
    [happens(tau)] -> [happens(tau')] -> equiv(frame@tau, 
seq(i:index -> if O(i) <= tau then output@O(i)), diff(s@tau',m)). 

Proof.
  induction tau => tau' Htau Htau'.

  (* Init *)
  expand frame@init.
  rewrite if_false  in 0 => //.
  fa 0.  

  use lastupdate_pure with tau' as [Hinit | [i HA]].
  
  use lastupdate_init with tau' as H; try auto.
  rewrite H. expand s@init. fresh 0. auto.

  use lastupdate_A with tau',i as H; try auto.
  rewrite H in *; expand s@A(i).
  prf 0; yesif 0; [2: by fresh 0].
  simpl. intro i' HAi'.
  use non_repeating with pred(A(i)),pred(A(i')) => //.
  by exists i'.
  by assumption.

  (* Oracle *)
  expand frame@O(i); fa 0; fa 1; fa 2. expand exec. fa 1. expand cond.
  splitseq 2: (fun(i0:index) -> O(i0) = O(i)).
  rewrite if_then_then in 2. 
  rewrite if_then_then in 3.
 
  assert (forall (i0:index), (O(i0) = O(i) && O(i0) <= O(i)) = (O(i0) =O(i))) as H1.
  intro i0.
  by rewrite eq_iff. 
  rewrite H1 in 2.

  assert (forall (i0:index), (not (O(i0) = O(i)) && O(i0) <= O(i)) = (O(i0) < O(i))) as H2.
  intro i0.
  by rewrite eq_iff. 
  rewrite H2 in 3.

  rewrite -le_pred_lt in 3.
  constseq 2: 
    (fun (i0:index) -> O(i0) = O(i)) (output@O(i)) 
    (fun (i0:index) -> O(i0) <> O(i)) zero.
  auto.
  split => i0 _; [1: by yesif | 2: by noif].
 
  expand output@O(i).
  fa 1.
  prf 1. (* Help. J'imagine qu'ici je dois faire prf pour m'en sortir mais alors la condition generee est toujours fause - a cause du premier element venant de l'imprecision dans le traiterement de la sequence - et du coup ne m'aide pas beaucoup. *)
admit 1. (* Du coup, j'admets ce point car je ne crois pas que je vais pouvoir m'en sortir *)

prf 1.
admit 1. (* Help. Meme probleme que ci-dessus *)

 
by apply IH.


  (* Tag *)
  expand frame@A(i). expand exec@A(i). expand cond@A(i). expand output@A(i).
  fa 0. fa 1. fa 1.
  rewrite le_lt in 2 => //.
  rewrite -le_pred_lt in 2.
  
 prf 1.
 yesif 1.
repeat split; project; repeat split.
intro i0 H. 

 (* Les deux admits ci-dessous pourraient disparaitre si on ameliore prf en presence du seq *)
 
assert (O(i0) < A(i)) by admit.
reach_equiv IH, A(i) => //. by fresh H.
intro i0 H. 
assert (O(i0) < A(i)) by admit.
reach_equiv IH, A(i) => //. by fresh H.

intro i0 H.
destruct H as [H|H].
destruct H as [i1 H].
destruct H as [H1 H2].
reach_equiv IH, A(i) => //. intro Hf; by fresh Hf.
reach_equiv IH, A(i) => //. intro Hf; by fresh Hf.

intro i0 H.
destruct H as [H|H].
destruct H as [i1 H].
destruct H as [H1 H2].
reach_equiv IH, A(i) => //. intro Hf; by fresh Hf.
reach_equiv IH, A(i) => //. intro Hf; by fresh Hf.

intro i0 H.
destruct H as [H|H].
destruct H as [i1 H].
destruct H as [H1 H2].

    use non_repeating with A(i),A(i0) => //. by exists i.
    use non_repeating with A(i),A(i0) => //; by exists i.

intro i0 H.
destruct H as [H|H].
destruct H as [i1 H].
destruct H as [H1 H2].

    use non_repeating with A(i),A(i0) => //; by exists i.

    use non_repeating with A(i),A(i0) => //; by exists i.
fresh 1.
apply IH => //.
Qed.
