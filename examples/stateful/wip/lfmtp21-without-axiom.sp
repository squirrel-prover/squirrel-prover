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
admit.

(*  expand frame@init.
  assert (seq(i:index->(if O(i) <= init then output@O(i))) = seq(i:index -> zero )) as Hseq.
  admit. (* a priori ok mais je ne sais pas le dire proprement *)
  rewrite Hseq in *.
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
    *)

  (* Oracle *)
(*
assert ((exists (i0:index), O(i0) <= pred(O(i)) && (input@O(i) = input@O(i0)))) as HnotUnique.
admit.
  expand frame. fa 0. fa 1. fa 2. expand exec. fa 1. expand cond.

assert(seq(i0:index->(if O(i0) <= O(i) then output@O(i0))) = seq(i0:index->(if O(i0) <= pred(O(i)) then output@O(i0)))).

destruct HnotUnique as [i' Hnot].

admit. (* vrai car output@O(i) est donne dans 1 *)
rewrite H in 2.

use IH with tau' => //.
(* on doit pouvoir supprimer 1 car il exists O(i0) dans la sequence qui donne le meme output *)
admit.

*)

(* assert ((forall (i0:index), O(i0) < O(i) => (input@O(i) <> input@O(i0)))) as Hunique.
admit. *)
expand frame@O(i).
fa 0.
fa 1. fa 2. expand exec. fa 1.  expand cond. 
expand output@O(i).
fa 1.
assert (exists i0: index, O(i0) < O(i) && input@O(i) = input@O(i0) ).
admit.

prf 1.

admit.

(*
expand output@O(i).
fa 1.


prf 1. 
yesif 1; 2: fresh 1.
simpl; split; project. split. intro i' H.
by use Hunique with i'.
by use Hunique with i'.
 intro i' H; try destruct H as [H|H].
by use Hunique with i'.
by use Hunique with i'.
 intro i' H. 
destruct H as [H|H].
destruct H as [H|H].
destruct H as [H|H].
destruct H as [H|H].
    reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.
    reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.
    reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.
    reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.
    reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.
intro i' H; try destruct H as [H|H].
destruct H as [H|H].
destruct H as [H|H].
  reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.
  reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.
  reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.   
 reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.yesif 1.

*)
  (* Tag *)
  expand frame@A(i). expand exec@A(i). expand cond@A(i). expand output@A(i).
  fa 0. fa 1. fa 1.
   assert(seq(i0:index->(if O(i0) <= A(i) then output@O(i0))) = seq(i0:index->(if O(i0) <= pred(A(i)) then output@O(i0)))) as Hseq.
admit. (* c'est ok car O(i0) = A(i) est impossible *)
rewrite Hseq in *.
  prf 1.
 yesif 1. 
repeat split; project; repeat split. 
reach_equiv IH, A(i) => //.
admit.
admit.

intro i0 H.
destruct H as [H|H].
destruct H as [H|H].
admit. 
reach_equiv IH, A(i) => //. intro Hf; by fresh Hf.
admit.

intro i0 H.
destruct H as [H|H].
destruct H as [H|H].
admit. 
reach_equiv IH, A(i) => //. intro Hf; by fresh Hf.
admit.

intro i0 H.
destruct H as [H|H].
destruct H as [H|H].

    use non_repeating with A(i),A(i0) => //. by exists i.
    use non_repeating with A(i),A(i0) => //; by exists i.

    use non_repeating with A(i),A(i0) => //. by exists i.

intro i0 H.
destruct H as [H|H].
destruct H as [H|H].

    use non_repeating with A(i),A(i0) => //; by exists i.

    use non_repeating with A(i),A(i0) => //; by exists i.
    use non_repeating with A(i),A(i0) => //; by exists i.
fresh 1.
apply IH => //.
Qed.
