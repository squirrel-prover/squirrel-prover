set autoIntro = false.

hash H.
hash G.
name k : message.
name k' : message.
name s0 : message.
mutable sT : message = s0.
mutable sR: message = s0.

abstract ok: message
channel o.
channel c.

system (
   (O: !_i in(o,x); out(o,<H(x,k),G(x,k')>)) |
   (T: !_i sT:=H(sT,k); out(c,G(sT,k'))) |
   (R: !_i in(c,x); if x = G(H(sR,k),k') then sR:=H(sR,k); out(c,ok)) 
).


axiom state : forall tau:timestamp, happens(tau) => (exists tau':timestamp, tau' < tau && sR@tau = sT@tau').
axiom statebis : forall tau:timestamp, happens(tau) => (exists tau':timestamp, tau' < tau && H(sR@tau,k) = sT@tau').

(** Last update lemmas: basic reasoning about the memory cell.
  * Here we decompose the usual lastupdate lemma to separate the "pure" part
  * from the part that involves message equalities. *)

goal lastupdateT_pure (tau:timestamp): 
  happens(tau) => (
    (forall j:index, happens(T(j)) => T(j)>tau) ||
    (exists i:index, happens(T(i)) && T(i) <=tau && 
     forall j:index, happens(T(j)) && T(j)<=tau => T(j)<=T(i))).
Proof.
induction tau.
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
case (T(j) <= pred( O(i))) => //.
use H23 with j => //.

(* T(i) *)
intro [i Eq]; subst tau, T(i); use IH with pred(T(i)) => //.
destruct H as [H1 | [i0 H2]];
try (right;
exists i;
repeat split => //).

(* R(i) *)
intro [i Eq]; subst tau, R(i); use IH with pred(R(i)) => //.
destruct H as [H1 | [i0 H2]].
left; intro j Hpj; by use H1 with j => //.
right; exists i0; repeat split =>//.
destruct H2 as [H21 H22 H23].
intro j [Hpj Ord].
case (T(j) <= pred( R(i))) => //.
use H23 with j => //.

(* R1(i) *)
intro [i Eq]; subst tau, R1(i); use IH with pred(R1(i)) => //.
destruct H as [H1 | [i0 H2]].
left; intro j Hpj; by use H1 with j => //.
right; exists i0; repeat split =>//.
destruct H2 as [H21 H22 H23].
intro j [Hpj Ord].
case (T(j) <= pred( R1(i))) => //.
use H23 with j => //.
Qed.


goal lastupdateT_init (tau:timestamp):
  happens(tau) => 
  (forall j:index, happens(T(j)) => T(j)>tau) => 
  sT@tau = sT@init.
Proof.
  induction tau => tau IH _ Htau.
  case tau;

  try(
  intro [i Hi]; rewrite Hi in *; expand sT;
  apply IH => //;
  intro j Hp; by use Htau with j).

  auto.

  intro [i Hi]; rewrite Hi in *.
  by use Htau with i.
Qed.

goal lastupdate_T (tau:timestamp,i:index):
  happens(T(i)) && 
  T(i)<=tau && 
  (forall j:index, happens(T(j)) && T(j)<=tau => T(j)<=T(i)) =>
  sT@tau = sT@T(i).
Proof.
  dependent induction tau => tau IH [Hinf Hsup].
  case tau.
 
  (* init *)
  intro H; rewrite H in Hinf; auto.

  (* O(i0) *)
  intro [j Hj]; rewrite Hj in *; expand sT@O(j).
  apply IH => //; simpl.
  intro k Hk; by use Hsup with k.

  (* T(i0) *)
  intro [j Hj]; rewrite Hj in *.
  assert i=j; [2: auto | 1: by use Hsup with j].
  
  (* R(i0) *)
  intro [j Hj]; rewrite Hj in *; expand sT@R(j).
  apply IH => //; simpl.
  intro k Hk; by use Hsup with k.

  (* R1(i0) *)
  intro [j Hj]; rewrite Hj in *; expand sT@R1(j).
  apply IH => //; simpl.
  intro k Hk; by use Hsup with k.
Qed.


goal lastupdateT (tau:timestamp):
  happens(tau) =>
  (sT@tau = sT@init && forall j:index, happens(T(j)) => T(j)>tau) ||
  (exists i:index, sT@tau = sT@T(i) && 
   happens(T(i)) && T(i)<=tau && 
   forall j:index, happens(T(j)) && T(j)<=tau => T(j)<=T(i)).
Proof.
  intro Htau.
  use lastupdateT_pure with tau as [Hinit|[i HAi]] => //.
  left; split => //; by apply lastupdateT_init.
  right; exists i; repeat split => //; by apply lastupdate_T.
Qed.

(* Reader *)

goal lastupdateR_pure (tau:timestamp):
  happens(tau) => (
  (forall j:index, happens(R(j)) => R(j)>tau) ||
  (exists i:index, happens(R(i)) && R(i)<=tau && 
   forall j:index, happens(R(j)) && R(j)<=tau => R(j)<=R(i))).
Proof.
induction tau.
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
case (R(j) <= pred( O(i))) => //.
use H23 with j => //.

(* T(i) *)
intro [i Eq]; subst tau, T(i); use IH with pred(T(i)) => //.
destruct H as [H1 | [i0 H2]].
left; intro j Hpj; by use H1 with j => //.
right; exists i0; repeat split =>//.
destruct H2 as [H21 H22 H23].
intro j [Hpj Ord].
case (R(j) <= pred( T(i))) => //.
use H23 with j => //.

(* R(i) *)
intro [i Eq]; subst tau, R(i); use IH with pred(R(i)) => //.
destruct H as [H1 | [i0 H2]];
try (right;
exists i;
repeat split => //).


(* R1(i) *)
intro [i Eq]; subst tau, R1(i); use IH with pred(R1(i)) => //.
destruct H as [H1 | [i0 H2]].
left; intro j Hpj; by use H1 with j => //.
right; exists i0; repeat split =>//.
destruct H2 as [H21 H22 H23].
intro j [Hpj Ord].
case (R(j) <= pred( R1(i))) => //.
use H23 with j => //.
Qed.


goal lastupdateR_init (tau:timestamp):
  happens(tau) => 
  (forall j:index, happens(R(j)) => R(j)>tau) => 
  sR@tau = sR@init.
Proof.
  induction tau => tau IH _ Htau.
  case tau;
  try(
  intro [i Hi]; rewrite Hi in *; expand sR;
  apply IH => //;
  intro j Hp; by use Htau with j).

  auto.

  intro [i Hi]; rewrite Hi in *.
  use Htau with i => //.
Qed.

goal lastupdate_R (tau:timestamp,i:index):
  happens(R(i)) && 
  R(i)<=tau && 
  (forall j:index, happens(R(j)) && R(j)<=tau => R(j)<=R(i)) =>
  sR@tau = sR@R(i).
Proof.
  dependent induction tau => tau IH [Hinf Hsup].
  case tau.
 
  (* init *)
  intro H; rewrite H in Hinf; auto.

  (* O(i0) *)
  intro [j Hj]; rewrite Hj in *; expand sR@O(j).
  apply IH => //; simpl.
  intro k Hk; by use Hsup with k.

  (* T(i0) *)
  intro [j Hj]; rewrite Hj in *; expand sR@T(j).
  apply IH => //; simpl.
  intro k Hk; by use Hsup with k.
  
  
  (* R(i0) *)
  intro [j Hj]; rewrite Hj in *.
  assert i=j; [2: auto | 1: by use Hsup with j].

  (* R1(i0) *)
  intro [j Hj]; rewrite Hj in *; expand sR@R1(j).
  apply IH => //; simpl.
  intro k Hk; by use Hsup with k.
Qed.


goal lastupdateR : forall tau:timestamp, happens(tau) =>
  (sR@tau = sR@init && forall j:index, happens(R(j)) => R(j)>tau) ||
  (exists i:index, sR@tau = sR@R(i) && happens(R(i)) && R(i)<=tau && forall j:index, happens(R(j)) && R(j)<=tau => R(j)<=R(i)).
Proof.
  intro tau Htau.
  use lastupdateR_pure with tau as [Hinit|[i HAi]] => //.
  left. split => //. by apply lastupdateR_init => //.
  
  right. exists i. repeat split => //. by apply lastupdate_R.
Qed.

(** The contents of the memory cell never repeats. *)

goal non_repeatingT :
  forall (beta,alpha:timestamp) happens(beta) =>
  (exists i:index, alpha < T(i) && T(i) <= beta) =>
  sT@alpha <> sT@beta.
Proof.
  induction => beta IH alpha _ [i [_ _]] Meq.
  use lastupdateT with beta as [[_ Habs] | [j [[_ _] Hsup]]]; 1: by use Habs with i.

  use Hsup with i => //.
  (* We now have alpha < T(i) <= T(j) < beta and no T(_) between T(j) and tau'. *)

  assert sT@alpha = sT@T(j) as Meuf => //; expand sT@T(j).
  euf Meuf => Heuf.

  use IH with pred(T(j)),pred(T(i0)) => //.
  by case Heuf; exists i0.

  assumption. (* TODO get rid of it earlier; also happens(beta) is consequence of _ <= beta *)
Qed.


goal non_repeatingR :
  forall (beta,alpha:timestamp) happens(beta) =>
  (exists i:index, alpha < R(i) && R(i) <= beta) =>
  sR@alpha <> sR@beta.
Proof.
  induction => beta IH alpha _ [i [_ _]] Meq.
  use lastupdateR with beta as [[_ Habs] | [j [[_ _] Hsup]]]; 1: by use Habs with i.

  use Hsup with i => //.
  (* We now have alpha < R(i) <= R(j) < beta and no R(_) between R(j) and tau'. *)

  assert sR@alpha = sR@R(j) as Meuf => //; expand sR@R(j).
  euf Meuf => Heuf.

  use IH with pred(R(j)),pred(R(i0)) => //.
  by case Heuf; exists i0.

  assumption. (* TODO get rid of it earlier; also happens(beta) is consequence of _ <= beta *)
Qed.


(** Strong secrecy *)

axiom unique_queries : forall (i,j:index) i <> j => input@O(i) <> input@O(j).


name m : message.




global goal [default/left,default/left]
  strong_secrecy (tau:timestamp) : forall (tau':timestamp),
    [happens(tau)] -> [happens(tau')] -> equiv(frame@tau, diff(sT@tau',m)).

Proof.
  induction tau => tau' Htau Htau'.

  (* Init *)
  expand frame@init.
  use lastupdateT_pure with tau' as [Hinit | [i HA]].

    use lastupdateT_init with tau' as H; try auto.
    rewrite H; expand sT@init; fresh 0; auto.

    use lastupdate_T with tau',i as H; try auto.
    rewrite H in *; expand sT@T(i).
    prf 0; yesif 0; [2: by fresh 0].
    simpl. intro i' HAi'.
    use non_repeatingT with pred(T(i)),pred(T(i')) => //.
    by exists i'.
  by assumption.

  (* Oracle *)
  expandall. fa 0. fa 1. fa 1. fa 1.
  
  (* Oracle H *)
  prf 1; yesif 1; 2: fresh 1.
  simpl; repeat split.
  intro i' H;   by apply unique_queries.

  intro i' H.     
  use state with  pred(R(i')) as [tau1 [H1 H2]].
  rewrite H2 in *.
  reach_equiv IH, tau1 => //; intro Hf; by fresh Hf; by auto.
  auto.
  
  intro i' H.     
  use state with  pred(R1(i')) as [tau1 [H1 H2]].
  rewrite H2 in *.
  reach_equiv IH, tau1 => //; intro Hf; by fresh Hf; by auto.
  auto.
  
  project.
  intro i' [H | H].
  reach_equiv IH,pred(T(i')) => //; intro Hf; by fresh Hf.
  reach_equiv IH,pred(T(i')) => //; intro Hf; by fresh Hf.
  intro i' H;  reach_equiv IH,pred(T(i')) => //; intro Hf; by fresh Hf.


  (* Oracle G *)
  prf 1. yesif 1; 2: fresh 1.
  simpl; repeat split.
   intro i' H; by apply unique_queries.
   intro i' H; reach_equiv IH,T(i') => //; intro Hf; by fresh Hf.

   intro i' H.
   assert (H(sR@pred(R(i')),k) = sR@R(i')).
   auto.
   rewrite Meq in *.
   use state with  R(i') as [tau1 [H1 H2]].
   rewrite H2 in *.
   reach_equiv IH, tau1 => //; intro Hf; by fresh Hf; by auto.
    auto.

   intro i' H.
   use statebis with pred(R1(i')) as [tau1 [H1 H2]]. 
   rewrite H2 in *.
   reach_equiv IH, tau1 => //; intro Hf; by fresh Hf; by auto.
   auto.

   by apply IH.

  (* Tag *)
  expand frame@T(i). expand exec@T(i). expand cond@T(i). expand output@T(i).
  fa 0. fa 1. fa 1.

  prf 1; yesif 1; 2: fresh 1.
  simpl;  repeat split.

  intro i' H; reach_equiv IH,T(i) => // Hf; by fresh Hf.
  intro i' H; use non_repeatingT with T(i),T(i') => //; by exists i.

    intro i' H.
   assert (H(sR@pred(R(i')),k) = sR@R(i')).
   auto.
   rewrite Meq in *.
  use state with  R(i') as [tau1 [H1 H2]] => //.
   rewrite H2 in *.
 use non_repeatingT with T(i),tau1 => //. exists i.
  by auto.


  intro i' H.
   use statebis with pred(R1(i')) as [tau1 [H1 H2]] => //. 
   rewrite H2 in *.
use non_repeatingT with T(i),tau1 => //. exists i.
  by auto.

  by apply IH.

(* Reader R(i) *)
 expand frame@R(i). 
  fa 0. fa 1.
  fa 2.
 expand output@R(i).
expand exec@R(i).
fa 1.
expand cond@R(i).
project.

equivalent
  exec@R(i),
exec@pred(R(i)) && exists j:index, T(j)<R(i) && input@R(i) = output@T(j).
admit. (* GAP entre le lemme prouve et celui qui permet d'utiliser fadup *)
expand output.
fadup 1.
by apply IH.

(* Reader R1(i) *)
expand frame@R1(i).
fa 0. fa 1.

equivalent
  exec@R1(i),
exec@pred(R1(i)) && not(exists j:index, T(j)<R1(i) && input@R1(i) = output@T(j)).
admit. (* GAP entre le lemme prouve et celui qui permet d'utiliser fadup *)
expand output.
fadup 1.
by apply IH.
Qed.





(* la valeur de l'etat du reader apparait dans l'etat du tag avant. Pour montrer cela, je suppose strong secrecy de l'etat du reader - c'est pour traiter le cas de l'oracle *)
global goal [default/left,default/left] GsR_implies_sT:
(* (forall (tau, tau': timestamp), [happens(tau)] -> [happens(tau')] -> equiv(frame@tau,diff(sT@tau',m))) 
-> *)
(forall (tau, tau': timestamp), [happens(tau)] -> [happens(tau')] -> equiv(frame@tau,diff(sR@tau',m))) 
->  [forall (tau1:timestamp), happens(tau1) => exec@tau1 => exists (tau2:timestamp), tau2 <= tau1 && sR@tau1 = sT@tau2].
Proof.
intro  HR.
induction.
intro tau1 IH.
intro Hp exec.
case tau1.

(* init *)
intro Eq.
exists init.
auto.

(* O(i) *)
intro [i Eq].
subst tau1, O(i).
expand exec@O(i).
destruct exec as [Hexec Hcond].
use IH with pred(O(i)) => //.
destruct H as [tau' [Hpred Eq]].
exists tau'.
split.
auto.
expand sR.
by assumption.

(* T(i) *)
intro [i Eq].
subst tau1, T(i).
expand exec@T(i).
destruct exec as [Hexec Hcond].
use IH with pred(T(i)) => //.
destruct H as [tau' [Hpred Eq]].
exists tau'.
split.
auto.
expand sR.
by assumption.


(* R(i) *)
intro [i Eq].
subst tau1, R(i).
expand exec@R(i).
destruct exec as [Hexec Hcond].
expand cond@R(i).
euf Hcond.

(* R(i) -cas de l'oracle *)
intro Ord.
assert(input@O(i0) <> H(sR@pred(R(i)),k)) =>//.
intro Eq.
assert(sR@R(i) = H(sR@pred(R(i)),k)).
expand sR@R(i).
auto.
assert( input@O(i0) <> sR@R(i)).
clear Hcond.
clear Hexec.
clear IH.
clear Eq.
clear Meq.
reach_equiv HR, R(i), R(i) => //.
intro Eq.
fresh Eq.
auto.
expand sR@R(i).
auto.


(* cas de l'etat du tag *)
intro Ord.
intro Eq.
expand sR@R(i).
exists T(i0).
split.
auto.
auto.

(* R1(i) *)
intro [i Eq].
subst tau1, R1(i).
expand exec@R1(i).
destruct exec as [Hexec Hcond].
use IH with pred(R1(i)) => //.
destruct H as [tau' [Hpred Eq]].
exists tau'.
split.
auto.
expand sR.
by assumption.
Qed.



(* a well-authentication goal with strong secrecy as an hypothesis *)

global goal [default/left,default/left] wa: 
(forall (tau, tau': timestamp), [happens(tau)] -> [happens(tau')] -> equiv(frame@tau,diff(sR@tau',m))) ->
[forall (i:index), happens(R(i)) => (exec@R(i) <=> 
(exec@pred(R(i)) &&
(exists j:index, T(j)<R(i) && input@R(i) = output@T(j) && sT@T(j) = sR@R(i))))].

Proof.
intro HR.
intro i.
intro Hp.

split.

(* => *) 
expand exec@R(i). expand cond@R(i).
intro [H1 Meq].
euf Meq.
(* cas de l'oracle *)
intro *.
split => //.
assert (H(sR@pred(R(i)),k) = sR@R(i)).
admit. (* c'est trivial mais je n'arrive pas a lui faire garder cette egalite en hypothese *)
assert (input@O(i0) = sR@R(i)).
auto.
assert (input@O(i0) <> sR@R(i)).
clear Meq1.
clear Meq0.
clear Meq.
clear H1.
reach_equiv HR, R(i), R(i) => //.
intro Eq.
fresh Eq.
auto.
auto.

(* cas du tag *)
intro *.
split => //.
exists i0.
auto.

(* <= *)
intro [j [H1 H2]].
expandall.
auto.
Qed.



