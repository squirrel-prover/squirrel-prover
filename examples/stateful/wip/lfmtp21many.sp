(* LMFTP'21 example with many tags,
 * i.e. OSK protocol without readers and with unique_queries axiom. *)

set autoIntro  = false.

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

axiom lastupdate_pure : forall (i:index,tau:timestamp), happens(tau) => (
  (forall j:index, happens(A(i,j)) => A(i,j)>tau) ||
  (exists j:index, 
    happens(A(i,j)) && A(i,j)<=tau 
    && forall jj:index, happens(A(i,jj)) && A(i,jj)<=tau => A(i,jj)<=A(i,j))).

axiom lastupdate_init : forall (i:index,tau:timestamp), happens(tau) => (
  (forall j:index, happens(A(i,j)) => A(i,j)>tau) 
  => s(i)@tau = s(i)@init).

axiom lastupdate_A : forall (i:index,j:index,tau:timestamp), happens(tau) => (
  (happens(A(i,j)) && A(i,j)<=tau 
    && forall jj:index, happens(A(i,jj)) && A(i,jj)<=tau => A(i,jj)<=A(i,j))
  => s(i)@tau = s(i)@A(i,j)).

axiom lastupdate : forall (i:index,tau:timestamp), happens(tau) => (
  (s(i)@tau = s(i)@init && forall j:index, happens(A(i,j)) => A(i,j)>tau) ||
  (exists j:index, 
    happens(A(i,j)) && s(i)@tau = s(i)@A(i,j) && A(i,j)<=tau 
    && forall jj:index, happens(A(i,jj)) && A(i,jj)<=tau => A(i,jj)<=A(i,j))).


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

goal monotonic_chain :
  forall (tau,tau':timestamp,i,j:index) happens(tau) =>
    tau = A(i,j) && tau' < tau => s(i)@tau' <> s(i)@tau.
Proof.
  induction => tau IH tau' i j Hap [H1 H2] Meq.
  subst tau, A(i,j).
  expand s(i)@A(i,j).
  euf Meq.
  intro Heuf Meuf *.
  use lastupdate with i0,pred(A(i,j)) as H1; 2: by auto.
  case H1.
    (* case H1 - init *)
    destruct H1 as [H1 H1'].
    use H1' with j0; 1,2: case Heuf; auto.
    (* case H1 - general *)
    admit. (* TODO *)
Qed.

goal non_repeating :
  forall (tau',tau:timestamp,i',i:index) happens(tau') =>
  (exists j:index, tau < A(i',j) && A(i',j) <= tau') =>
  s(i)@tau <> s(i')@tau'.
Proof.
  induction => tau' IH tau i' i _ [j [_ _]] Meq.
  use lastupdate with i',tau' as [[_ Habs] | [j' [[_ _] Hsup]]] => //; 
    1: by use Habs with j.

  use Hsup with j as _ => //.
  (* We now have tau < A(i',j) <= A(i',j') <= tau' 
     and no A(i',_) between A(i',j') and tau'. *)

  assert s(i)@tau = s(i')@A(i',j') as Meuf => //; expand s(i')@A(i',j');
    euf Meuf => Heuf_ts Heuf_msg.

  use IH with pred(A(i',j')),pred(A(i0,j0)),i',i0 => //.
  admit.
  (* TODO coincé: on ne peut pas forcément trouver d'action A(i',_) entre
       pred(A(i0,j0)) et pred(A(i',j')).
       Avec un seul tag on était en gros dans la situation où i0=i'
       et j0 convenait. *)
Qed.

(** Strong secrecy *)

axiom unique_queries : forall (i,j:index) i <> j => input@O(i) <> input@O(j).

name m : message.

global goal [default/left,default/left]
  strong_secrecy (tau:timestamp) : forall (i':index,tau':timestamp),
    [happens(tau)] -> [happens(tau')] -> equiv(frame@tau, diff(s(i')@tau',m)).
Proof.
  induction tau => i' tau' Htau Htau'.

  (* Init *)
  expand frame@init.
  use lastupdate_pure with i',tau' as [Hinit | [j HA]]; try auto.

    use lastupdate_init with i',tau' as H; try auto.
    rewrite H; expand s(i')@init; fresh 0; auto.

    use lastupdate_A with i',j,tau' as H; try auto.
    rewrite H in *; expand s(i')@A(i',j).
    prf 0; yesif 0; [2: by fresh 0].
    simpl. intro i0 j0 HAi0.
    assert i'=i0 || i'<>i0; try auto.
    case H0.
    admit. (* use monotonic_chain with pred(A(i',j)),pred(A(i0,j0)),i',i0 => //. *)
    use disjoint_chains with pred(A(i',j)),pred(A(i0,j0)),i',i0 => //.

  (* Oracle *)
  expandall. fa 0. fa 1. fa 1. fa 1.
  prf 1; yesif 1; 2: fresh 1.
  simpl; split; project. 
    intro j0 H; try destruct H as [H|H].
    admit.(* TODO le raffinement de PRF ne suffit pas: l'oracle ne peut venir de s@tau *)
    apply unique_queries; auto.
    intro i0 j0 H.
    reach_equiv IH,i0,pred(A(i0,j0)) => // Hf; by fresh Hf.
    intro i0 j0 H; try destruct H as [H|H].
    reach_equiv IH,i0,pred(A(i0,j0)) => // Hf; by fresh Hf.
    reach_equiv IH,i0,pred(A(i0,j0)) => // Hf; by fresh Hf.
    intro j0 H.
    apply unique_queries; auto.
  prf 1; yesif 1; 2: fresh 1; by apply IH.
  simpl; split; project.
    intro j0 H; try destruct H as [H|H].
    admit. (* TODO as above *)
    apply unique_queries; auto.
    intro i0 j0 H.
    reach_equiv IH,i0,A(i0,j0) => // Hf; by fresh Hf.
    intro i0 j0 H; try destruct H as [H|H].
    reach_equiv IH,i0,A(i0,j0) => // Hf; by fresh Hf.
    reach_equiv IH,i0,A(i0,j0) => // Hf; by fresh Hf.
    intro j0 H.
    apply unique_queries; auto.

  (* Tag *)
  expand frame@A(i,j). expand exec@A(i,j). expand cond@A(i,j). expand output@A(i,j).
  fa 0. fa 1. fa 1.
  prf 1; yesif 1; 2: fresh 1; by apply IH.
  simpl; split; project.
    intro j0 H; try destruct H as [H|H].
    admit. (* TODO as above *)
    reach_equiv IH,i,A(i,j) => // Hf; by fresh Hf.
    intro i0 j0 H.
    assert i=i0 || i<>i0; try auto.
    case H0.
    use monotonic_chain with A(i,j),A(i,j0),i,j => //.
    use disjoint_chains with A(i,j),A(i0,j0),i,i0 => //.
    intro i0 j0 H; try destruct H as [H|H].
    assert i=i0 || i<>i0; try auto.
    case H0.
    admit. (* use monotonic_chain with A(i,j),A(i0,j0),i',i0 => //. *)
    use disjoint_chains with A(i,j),A(i0,j0),i,i0 => //.
    assert i=i0 || i<>i0; try auto.
    case H0.
    use monotonic_chain with A(i,j),A(i,j0),i,j => //.
    use disjoint_chains with A(i,j),A(i0,j0),i,i0 => //.
    intro j0 H.
    reach_equiv IH,i,A(i,j) => // Hf; by fresh Hf.
Qed.
