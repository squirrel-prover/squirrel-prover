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



(** Last update lemmas: basic reasoning about the memory cell.
  * Here we decompose the usual lastupdate lemma to separate the "pure" part
  * from the part that involves message equalities. *)

goal lastupdateT_pure : forall tau:timestamp,
  (forall j:index, T(j)>tau) ||
  (exists i:index, T(i)<=tau && forall j:index, T(j)<=tau => T(j)<=T(i)).
Proof.
admit. (* ok - en fait je ne sais pas trop comment faire une telle preuve - Doit-on mettre une hyp Happens?*)
Qed.


goal lastupdateT_pure_bis : forall tau:timestamp, happens(tau) => (
  (forall j:index, happens(T(j)) => T(j)>tau) ||
  (exists i:index, happens(T(i)) && T(i)<=tau && forall j:index, happens(T(j)) => (T(j)<=tau => T(j)<=T(i)))).
Proof.
induction.
intro tau IH Hp.

case tau.

(* init *)
intro Eq.
left.
intro j Hpj.
auto.

(* O(i) *)
intro [i Eq].
subst tau, O(i).
use IH with pred(O(i)) => //.
destruct H as [H1 | [i0 H2]].
left.
intro j Hpj.
use H1 with j => //.
right.
exists i0.
repeat split =>//.
destruct H2 as [H21 H22 H23].
intro j Hpj Ord.
case (T(j) <= pred( O(i))) => //.
use H23 with j => //.

(* T(i) *)
admit. 

(* R(i) *)
admit.

(* R1(i) *)
admit.
Qed.

goal lastupdateT_init :
  forall tau:timestamp, happens(tau) => (forall j:index, T(j)>tau) => sT@tau = sT@init.
Proof.
  induction => tau IH _ Htau.
  case tau; 
  try(
  intro [i Hi]; rewrite Hi in *; expand sT;
  apply IH => //;
  intro j; by use Htau with j).

  auto.

  intro [i Hi]; rewrite Hi in *.
  by use Htau with i.
Qed.

goal lastupdate_T :
  forall (tau:timestamp,i:index)
  (T(i)<=tau && forall j:index, T(j)<=tau => T(j)<=T(i)) =>
  sT@tau = sT@T(i).
Proof.
  induction => tau IH _ [Hinf Hsup].
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


goal lastupdateT : forall tau:timestamp, happens(tau) =>
  (sT@tau = sT@init && forall j:index, T(j)>tau) ||
  (exists i:index, sT@tau = sT@T(i) && T(i)<=tau && forall j:index, T(j)<=tau => T(j)<=T(i)).
Proof.
  intro tau Htau.
  use lastupdateT_pure with tau as [Hinit|[i HAi]] => //.
  left; split => //; by apply lastupdateT_init.
  right; exists i; repeat split => //; by apply lastupdate_T.
Qed.

(* Reader *)

goal lastupdateR_pure : forall tau:timestamp,
  (forall j:index, R(j)>tau) ||
  (exists i:index, R(i)<=tau && forall j:index, R(j)<=tau => R(j)<=R(i)).
Proof.
admit. (* ok - en fait je ne sais pas trop comment faire une telle preuve - Doit-on mettre une hyp Happens?*)
Qed.

goal lastupdateR_init :
  forall tau:timestamp, happens(tau) => (forall j:index, R(j)>tau) => sR@tau = sR@init.
Proof.
  induction => tau IH _ Htau.
  case tau; 
  try(
  intro [i Hi]; rewrite Hi in *; expand sR;
  apply IH => //;
  intro j; by use Htau with j).

  auto.

  intro [i Hi]; rewrite Hi in *.
  by use Htau with i.
Qed.

goal lastupdate_R :
  forall (tau:timestamp,i:index)
  (R(i)<=tau && forall j:index, R(j)<=tau => R(j)<=R(i)) =>
  sR@tau = sR@R(i).
Proof.
  induction => tau IH _ [Hinf Hsup].
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
  (sR@tau = sR@init && forall j:index, R(j)>tau) ||
  (exists i:index, sR@tau = sR@R(i) && R(i)<=tau && forall j:index, R(j)<=tau => R(j)<=R(i)).
Proof.
  intro tau Htau.
  use lastupdateR_pure with tau as [Hinit|[i HAi]] => //.
  left; split => //; by apply lastupdateR_init.
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

  use Hsup with i as _; 2: assumption.
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

  use Hsup with i as _; 2: assumption.
  (* We now have alpha < R(i) <= R(j) < beta and no R(_) between R(j) and tau'. *)

  assert sR@alpha = sR@R(j) as Meuf => //; expand sR@R(j).
  euf Meuf => Heuf.

  use IH with pred(R(j)),pred(R(i0)) => //.
  by case Heuf; exists i0.

  assumption. (* TODO get rid of it earlier; also happens(beta) is consequence of _ <= beta *)
Qed.


(** Strong secrecy *)

axiom unique_queries : forall (i,j:index) i <> j => input@O(i) <> input@O(j).



goal well_auth :
  forall (i:index) happens(R(i)) => 
(exec@R(i) <=> 
(exec@pred(R(i)) &&
(exists j:index, T(j)<R(i) && input@R(i) = output@T(j) && sT@T(j) = sR@R(i)))).

Proof.
intro *.

split.

(* => *) 
expand exec@R(i). expand cond@R(i).
intro [H1 Meq].
euf Meq.
(* cas de l'oracle *)
intro *.
split => //.
admit. (* il faudrait pouvoir invoquer le secrecy de l'état du reader *)
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

  (* Oracle *)
  expandall. fa 0. fa 1. fa 1. fa 1.
  
  (* Oracle H *)
  prf 1; yesif 1; 2: fresh 1.
  simpl; split; project; repeat split; intro i' H; try destruct H as [H|H].
  admit. (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
  by apply unique_queries.
  reach_equiv IH,pred(T(i')) => //; intro Hf; by fresh Hf.
  reach_equiv IH,pred(T(i')) => //; intro Hf; by fresh Hf.
  admit. (* sR ?*)
admit. (* sR ?*)
    admit. (* sR ?*)
  admit. (* sR ?*)
  
reach_equiv IH,pred(T(i')) => //; intro Hf; by fresh Hf.
  admit. (* sR ?*)
 admit. (* sR ?*)
  by apply unique_queries.

  (* Oracle G *)
  prf 1. yesif 1; 2: fresh 1.
  simpl; split; project; repeat split; intro i' H; try destruct H as [H|H].


   admit.  (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
   by apply unique_queries.
   reach_equiv IH,T(i') => //; intro Hf; by fresh Hf.
   reach_equiv IH,T(i') => //; intro Hf; by fresh Hf.
admit. (* sR ?*)
admit. (* sR ?*)
admit. (* sR ?*)
admit. (* sR ?*)
   reach_equiv IH,T(i') => //; intro Hf; by fresh Hf.
admit. (* sR ?*)
admit. (* sR ?*)

   by apply unique_queries.

   by apply IH.

  (* Tag *)
  expand frame@T(i). expand exec@T(i). expand cond@T(i). expand output@T(i).
  fa 0. fa 1. fa 1.

  prf 1; yesif 1; 2: fresh 1.
  simpl; split; project; repeat split; intro i' H; try destruct H as [H|H].


  admit.  (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
  (* Ok mais pourquoi je ne peux pas faire reach_equiv IH,A(i) => //.*)
  reach_equiv IH,T(i) => // Hf; by fresh Hf.
  admit. (* ok si PRF plus fin *)
  use non_repeatingT with T(i),T(i') => //; by exists i.
  admit.  (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
  admit. (* sR *)  
  admit. (* sR *)  
admit. (* sR *)  

use non_repeatingT with T(i),T(i') => //; by exists i.
admit. (* prf plus fin *)
admit. (* sR *)
  reach_equiv IH,T(i) => // Hf; by fresh Hf.

  by apply IH.

(* Reader R(i) *)
 expand frame@R(i). 
  fa 0. fa 1.

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

