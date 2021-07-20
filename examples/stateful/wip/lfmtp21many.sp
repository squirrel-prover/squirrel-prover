(* LMFTP'21 example with many tags,
 * i.e. OSK protocol without readers and with unique_queries axiom. *)

set autoIntro = false.

hash H.
hash G.
name k : message.
name k' : message.
name s0 : index->message.
mutable s (i:index) : message = s0(i).

channel o.
channel c.

system (
   (O: !_j in(o,x); out(o,<H(x,k),G(x,k')>)) |
   (A: !_i !_j s(i):=H(s(i),k); out(o,G(s(i),k')))
).


(** Last update lemmas: basic reasoning about the memory cell.
  * Here we decompose the usual lastupdate lemma to separate the "pure" part
  * from the part that involves message equalities. *)

axiom lastupdate_pure : forall (i:index,tau:timestamp),
  (forall j:index, A(i,j)>tau) ||
  (exists j:index, A(i,j)<=tau && forall jj:index, A(i,jj)<=tau => A(i,jj)<=A(i,j)).

axiom lastupdate_init :
  forall (i:index,tau:timestamp), happens(tau) => (forall j:index, A(i,j)>tau) => s(i)@tau = s(i)@init.

axiom lastupdate_A :
  forall (i:index,tau:timestamp,j:index)
  (A(i,j)<=tau && forall jj:index, A(i,j)<=tau => A(i,jj)<=A(i,j)) =>
  s(i)@tau = s(i)@A(i,j).

axiom lastupdate : forall (i:index,tau:timestamp), happens(tau) =>
  (s(i)@tau = s(i)@init && forall j:index, A(i,j)>tau) ||
  (exists j:index, s(i)@tau = s(i)@A(i,j) && A(i,j)<=tau && forall jj:index, A(i,jj)<=tau => A(i,jj)<=A(i,j)).


(** The contents of the memory cell never repeats. *)


(** An attempt at something simpler than non_repeating,
    where we don't need to maintain the assumption (tau < A(i',_) <= tau')
    when using the induction hypothesis. This allows to conclude
    using collision in one case... but I'm stuck with the init cases. *)
goal disjoint_chains :
  forall (tau',tau:timestamp,i',i:index) happens(tau',tau) =>
  i<>i' =>
  s(i)@tau <> s(i')@tau'.
Proof.
  induction => tau' IH tau i' i _ _ Meq.
  use lastupdate with i,tau as [[_ Hinit] | [j [[_ _] Hsup]]] => //;
  use lastupdate with i',tau' as [[_ Hinit'] | [j' [[_ _] Hsup']]] => //.
admit. (* TODO s0(i) <> s(i')@A(i',j') *)
admit. (* TODO s0(i') <> s(i)@A(i,j) *)
  assert H(s(i)@pred(A(i,j)),k) = H(s(i')@pred(A(i',j')),k) as Hcoll;
    1: by expandall.
  collision Hcoll => H.
  use IH with pred(A(i',j')),pred(A(i,j)),i',i => //.
Qed.

goal non_repeating :
  forall (tau',tau:timestamp,i',i:index) happens(tau') =>
  (exists j:index, tau < A(i',j) && A(i',j) <= tau') =>
  s(i)@tau <> s(i')@tau'.
Proof.
  induction => tau' IH tau i' i _ [j [_ _]] Meq.
  use lastupdate with i',tau' as [[_ Habs] | [j' [[_ _] Hsup]]] => //; 1: by use Habs with j.

  use Hsup with j as _; 2: assumption.
  (* We now have tau < A(i',j) <= A(i',j') < tau' and no A(i',_) between A(i',j') and beta. *)

  assert s(i)@tau = s(i')@A(i',j') as Meuf => //; expand s(i')@A(i',j');
    euf Meuf => Heuf_ts Heuf_msg.

  use IH with pred(A(i',j')),pred(A(i0,j0)),i',i0 => //.
  (* TODO coincé: on ne peut pas forcément trouver d'action A(i',_) entre
       pred(A(i0,j0)) et pred(A(i',j')).
       Avec un seul tag on était en gros dans la situation où i0=i'
       et j0 convenait. *)
Qed.

(** ---------------------------------------------------------------------------------- **)
(* Non mis à jour ci-dessous *)

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
  prf 1; yesif 1; 2: fresh 1.
  simpl; split; project; intro i' H; try destruct H as [H|H];
    try by apply unique_queries.
    admit. (* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
    reach_equiv IH,pred(A(i')) => //.
      intro Hf; by fresh Hf.
    reach_equiv IH,pred(A(i')) => // Hf; by fresh Hf.
    reach_equiv IH,pred(A(i')) => // Hf; by fresh Hf.
  prf 1; yesif 1; 2: fresh 1; by apply IH.
  simpl; split; project; intro i' H; try destruct H as [H|H];
    try by apply unique_queries.
    admit. (* TODO as above *)
    reach_equiv IH,A(i') => // Hf; by fresh Hf.
    reach_equiv IH,A(i') => // Hf; by fresh Hf.
    reach_equiv IH,A(i') => // Hf; by fresh Hf.

  (* Tag *)
  expand frame@A(i). expand exec@A(i). expand cond@A(i). expand output@A(i).
  fa 0. fa 1. fa 1.
  prf 1; yesif 1; 2: fresh 1; by apply IH.
  simpl; split; project; intro i' H; try destruct H as [H|H].
    admit. (* TODO as above *)
    reach_equiv IH,A(i) => // Hf; by fresh Hf.
    use non_repeating with A(i),A(i') => //; by exists i.
    admit. (* TODO as above *)
    use non_repeating with A(i),A(i') => //; by exists i.
    reach_equiv IH,A(i) => // Hf; by fresh Hf.
Qed.
