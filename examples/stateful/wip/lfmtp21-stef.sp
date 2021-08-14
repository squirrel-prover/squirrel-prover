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

axiom lastupdate_pure : forall tau:timestamp,
  (forall j:index, A(j)>tau) ||
  (exists i:index, A(i)<=tau && forall j:index, A(j)<=tau => A(j)<=A(i)).

goal lastupdate_init :
  forall tau:timestamp, happens(tau) => (forall j:index, A(j)>tau) => s@tau = s@init.
Proof.
  induction => tau IH _ Htau.
  case tau.

  auto.

  intro [i Hi]; rewrite Hi in *; expand s@O(i).
  apply IH => //.
  intro j; by use Htau with j.

  intro [i Hi]; rewrite Hi in *.
  by use Htau with i.
Qed.

goal lastupdate_A :
  forall (tau:timestamp,i:index)
  (A(i)<=tau && forall j:index, A(j)<=tau => A(j)<=A(i)) =>
  s@tau = s@A(i).
Proof.
  induction => tau IH _ [Hinf Hsup].
  case tau.

  intro H; rewrite H in Hinf; auto.

  intro [j Hj]; rewrite Hj in *; expand s@O(j).
  apply IH => //; simpl.
  intro k Hk; by use Hsup with k.

  intro [j Hj]; rewrite Hj in *.
  assert i=j; [2: auto | 1: by use Hsup with j].
Qed.

goal lastupdate : forall tau:timestamp, happens(tau) =>
  (s@tau = s@init && forall j:index, A(j)>tau) ||
  (exists i:index, s@tau = s@A(i) && A(i)<=tau && forall j:index, A(j)<=tau => A(j)<=A(i)).
Proof.
  intro tau Htau.
  use lastupdate_pure with tau as [Hinit|[i HAi]] => //.
  left; split => //; by apply lastupdate_init.
  right; exists i; repeat split => //; by apply lastupdate_A.
Qed.


(** The contents of the memory cell never repeats. *)

goal non_repeating :
  forall (beta,alpha:timestamp) happens(beta) =>
  (exists i:index, alpha < A(i) && A(i) <= beta) =>
  s@alpha <> s@beta.
Proof.
  induction => beta IH alpha _ [i [_ _]] Meq.
  use lastupdate with beta as [[_ Habs] | [j [[_ _] Hsup]]]=> //; 1: by use Habs with i.

  use Hsup with i as _; 2: assumption.
  (* We now have alpha < A(i) <= A(j) < beta and no A(_) between A(j) and tau'. *)

  assert s@alpha = s@A(j) as Meuf => //; expand s@A(j); euf Meuf => Heuf.

  use IH with pred(A(j)),pred(A(i0)) => //.
  by case Heuf; exists i0.

Qed.


(** Strong secrecy *)

axiom unique_queries : forall (i,j:index) i <> j => input@O(i) <> input@O(j).

name m : message.

global goal [default/left,default/left]
  strong_secrecy (tau:timestamp) : forall (tau':timestamp),
    [happens(tau)] -> [happens(tau')] -> equiv(frame@tau, diff(s@tau',m)).
Proof.
  induction tau => tau' Htau Htau'.

  (* Init *)
  expand frame@init.
  use lastupdate_pure with tau' as [Hinit | [i HA]].

    use lastupdate_init with tau' as H; try auto.
    rewrite H; expand s@init; fresh 0; auto.

    use lastupdate_A with tau',i as H; try auto.
    rewrite H in *; expand s@A(i).
    prf 0; yesif 0; [2: by fresh 0].
    simpl. intro i' HAi'.
    use non_repeating with pred(A(i)),pred(A(i')) => //.
    by exists i'.

  (* Oracle *)
  expandall. fa 0. fa 1. fa 1. fa 1.
  
  (* Oracle H *)
  prf 1; yesif 1; 2: fresh 1.
  simpl; split; project; intro i' H; try destruct H as [H|H].
  admit. (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
  by apply unique_queries.
  reach_equiv IH,pred(A(i')) => //; intro Hf; by fresh Hf.
  reach_equiv IH,pred(A(i')) => //; intro Hf; by fresh Hf.
  reach_equiv IH,pred(A(i')) => //; intro Hf; by fresh Hf.
  by apply unique_queries.

  (* Oracle G *)
  prf 1. yesif 1; 2: fresh 1.
  simpl; split; project; intro i' H; try destruct H as [H|H].
   admit.  (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
   by apply unique_queries.
   reach_equiv IH,A(i') => //; intro Hf; by fresh Hf.
   reach_equiv IH,A(i') => //; intro Hf; by fresh Hf.
   reach_equiv IH,A(i') => //; intro Hf; by fresh Hf.
   by apply unique_queries.

   by apply IH.

  (* Tag *)
  expand frame@A(i). expand exec@A(i). expand cond@A(i). expand output@A(i).
  fa 0. fa 1. fa 1.
  prf 1; yesif 1; 2: fresh 1.
  simpl; split; project; intro i' H; try destruct H as [H|H].

  admit.  (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
  (* Ok mais pourquoi je ne peux pas faire reach_equiv IH,A(i) => //.*)
  reach_equiv IH,A(i) => // Hf; by fresh Hf.
  use non_repeating with A(i),A(i') => //; by exists i.
  admit.  (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
  use non_repeating with A(i),A(i') => //; by exists i.
  reach_equiv IH,A(i) => // Hf; by fresh Hf.

  by apply IH.

Qed.
