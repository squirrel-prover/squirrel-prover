(*******************************************************************************
RUNNING EXAMPLE

This protocol is a variant of the OSK protocol described in:
M. Ohkubo, K. Suzuki, S. Kinoshita et al.,
“Cryptographic approach to “privacy-friendly” tags,”
RFID privacy workshop, vol. 82. Cambridge, USA, 2003.

Each tag is associated to a mutable state sT initialized with s0.
Readers have access to a database containing an entry sR for each authorized
tag.

         sT := H(sT,k)
T -> R : G(sT,k')

         input x; sR := H(sR,k) if x = G(H(sR,k),k') with sR in DB
R -> T : ok

COMMENTS
- In this model we add in parallel a process in order to provide the attacker
the ability to compute hashes with their respective keys (without knowing these
keys).
- The reader process is not modelled here, this is left for future work.

HELPING LEMMAS
- last update
- disjoint chains
- monotonic chain

SECURITY PROPERTIES
- strong secrecy
*******************************************************************************)
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

include Basic.

(* AXIOMS *)

(* We assume that the attacker never repeats a query to the oracle. *)

axiom unique_queries (i,j:index) : i <> j => input@O(i) <> input@O(j).

(* HELPING LEMMAS *)

(* See `running-ex.sp` for more details about lastupdate_XXX lemmas. *)

lemma lastupdate_pure : forall (i:index,tau:timestamp), happens(tau) => (
  (forall j, happens(A(i,j)) => A(i,j)>tau) ||
  (exists j, happens(A(i,j)) && A(i,j)<=tau
    && forall jj, happens(A(i,jj)) && A(i,jj)<=tau => A(i,jj)<=A(i,j))).

Proof.
  intro i.
  induction => tau IH Hp.
  case tau.

    + (* init *)
      intro Eq; by left.

    + (* O(i) *)
      intro [j Eq]; rewrite Eq in *; clear Eq.
      use IH with pred(O(j)) => //.
      destruct H as [H1 | [j0 H2]].
        - left; intro j0 HpA; by use H1 with j0.
        - right.
          destruct H2 as [_ _ H2].
          exists j0.
          intro /= jj Hyp.
          by apply H2.

    + (* A(i0,j) *)
      intro [i0 j Eq]; rewrite Eq in *; clear Eq.
      case (i<>i0) => //.
       - (* 1st case: i<>i0 *)
          intro Neq.
          use IH with pred(A(i0,j)) => //.
          destruct H as [H1 | [j0 H2]].
            * left; intro j0 HpA; by use H1 with j0.
            * right; destruct H2 as [_ _ H2]; exists j0.
              intro /= jj Hyp.
              by apply H2.

      - (* 2nd case: i<>i0 *)
        intro Eq /=. 
        by right; exists j.
Qed.

global lemma lastupdate_pure_glob :
  Forall (i:index[const], tau:timestamp[const]),
  [happens(tau)] -> (
    [forall (j:index), happens(A(i,j)) => A(i,j)>tau] \/
    (Exists (j:index[const]),
      [happens(A(i,j)) && A(i,j) <= tau] /\
      [forall (jj:index), happens(A(i,jj)) && A(i,jj)<=tau => A(i,jj)<=A(i,j)])).
Proof.
  intro i.
  dependent induction => tau IH Hp.
  case tau.

    + (* init *)
      intro Eq; by left.

    + (* O(i) *)
      intro [j Eq]; rewrite Eq in *; clear Eq.
      use IH with pred(O(j)) => //.
      destruct H as [H1 | [j0 H2]].
        - left; intro j0 HpA; by use H1 with j0.
        - right.
          destruct H2 as [[_ _] H2].
          exists j0. 
          split; 1: auto. 
          intro /= jj Hyp.
          by apply H2.

    + (* A(i0,j) *)
      intro [i0 j Eq]; rewrite Eq in *; clear Eq.
      ghave [Neq | Eq] : [i <> i0 || i = i0]; 1:auto. 
       - (* 1st case: i<>i0 *)
          use IH with pred(A(i0,j)) => //.
          destruct H as [H1 | [j0 H2]].
            * left; intro j0 HpA; by use H1 with j0.
            * right; destruct H2 as [[_ _] H2]; exists j0.
              split; 1:auto.
              intro /= jj Hyp.
              by apply H2.

      - (* 2nd case: i<>i0 *)
        right; exists j. 
        by split.
Qed.

lemma lastupdate_init : forall (i:index,tau:timestamp), happens(tau) => (
  (forall j, happens(A(i,j)) => A(i,j)>tau))
  => s(i)@tau = s(i)@init.

Proof.
  intro i.
  induction => tau IH Htau.
  case tau.

    + (* init *)
      by auto.

    + (* O(j) *)
      intro [j Hj]; rewrite Hj in *.
      expand s(i)@O(j).
      intro Hyp.
      use IH with pred(O(j)) => //.
      intro j0 HpA.
      by use Hyp with j0.

    + (* A(i0,j) *)
      intro [i0 j HA]; rewrite HA in *.
      case (i = i0) => //.
        - intro Eq H0.
          use H0 with j => //.

        - intro Neq H0.
          use IH with pred(A(i0,j)) => //.
            * expand s(i)@A(i0,j).
              rewrite if_false => //.
            * intro j0 Hp.
              use H0 with j0 => //.
Qed.


lemma lastupdate_A: forall (i:index, j:index, tau:timestamp),
  (happens(tau) &&
   A(i,j)<=tau &&
   forall jj, happens(A(i,jj)) && A(i,jj)<=tau => A(i,jj)<=A(i,j))
  => s(i)@tau = s(i)@A(i,j).
Proof.
  intro i j.
  induction => tau IH [Hp Ord Hyp].
  case tau.

    + (* init *)
      by auto.

    + (* O(j0 *)
      intro [j0 Hj]; rewrite Hj in *.
      expand s(i)@O(j0).
      use IH with pred(O(j0)) => //.
      repeat split => //.
      intro jj H.
      use Hyp with jj => //.

    + (* A(i0,j0) *)
      intro [i0 j0 H]; rewrite H in *.
      case (i=i0) => //.
        - intro Eqi.
          use Hyp with j0.
            * case (j=j0); [1: by rewrite if_true | 2:auto].
            * auto.
        - intro Neqi.
          rewrite if_false.
            * auto.
            * use IH with pred(A(i0,j0)) => //.
              repeat split => //.
              intro jj H0.
              use Hyp with jj => //.
Qed.


lemma lastupdate : forall (i:index,tau:timestamp), happens(tau) => (
  (s(i)@tau = s(i)@init && forall j, happens(A(i,j)) => A(i,j)>tau) ||
  (exists j,
    s(i)@tau = s(i)@A(i,j) && A(i,j)<=tau
    && forall jj, happens(A(i,jj)) && A(i,jj)<=tau => A(i,jj)<=A(i,j))).
Proof.
  intro i tau Htau.
  use lastupdate_pure with i, tau as [Hinit | [j [HAj1 HAj2 HAj3]]] => //.
    + left.
      split => //.
      by apply lastupdate_init.
    + right.
      exists j.
      repeat split => //.
      use lastupdate_A with i, j, tau => //.
Qed.

(** The contents of distinct memory cells never coincide. *)

lemma disjoint_chains :
  forall (tau',tau:timestamp,i',i:index), happens(tau',tau) =>
  i<>i' =>
  s(i)@tau <> s(i')@tau'.
Proof.
  induction => tau' IH tau i' i D E Meq.
  use lastupdate with i,tau as [[A0 Hinit] | [j [A0 A1 Hsup]]] => //;
  use lastupdate with i',tau' as [[A Hinit'] | [j' [B C Hsup']]] => //.

    + rewrite -Meq A0 /s in B.
      by fresh B.

    + rewrite Meq A /s in A0.
      by fresh A0.

    + rewrite Meq B /s in A0.
      collision A0 => H.
      use IH with pred(A(i',j')),pred(A(i,j)),i',i => //.
Qed.

(** Values do not repeat inside the same chain of hashes. *)

lemma monotonic_chain :
  forall (tau,tau':timestamp,i,j:index), happens(tau,A(i,j)) => (
    (s(i)@tau = s(i)@A(i,j) && tau' < A(i,j) && A(i,j) <= tau)
    => s(i)@tau' <> s(i)@tau).
Proof.
  induction => tau IH tau' i j Hap [H1 H2 H3] Meq.
  assert s(i)@tau' = s(i)@A(i,j) as Meq' by auto.
  expand s(i)@A(i,j).
  euf Meq'.
  intro [j0 [Heuf Meuf]].
    use lastupdate with i,pred(A(i,j)) as H4; 2: by auto.
    case H4.
      - (* case H4 - init *)
        destruct H4 as [H4 H4'].
        use H4' with j0; by case Heuf. 
      - (* case H1 - general *)
        destruct H4 as [j1 [Meq1 H4 H5]].
        use IH with pred(A(i,j)), pred(A(i,j0)),i,j1 as H; try auto.
        use H5 with j0; by case Heuf.
Qed.


(* SECURITY PROPERTIES *)

name m : message.

global lemma [default/left,default/left]
  strong_secrecy (tau:timestamp[const]) : 
  Forall (i':index[const],tau':timestamp[const]),
    [happens(tau)] -> [happens(tau')] -> equiv(frame@tau, diff(s(i')@tau',m)).
Proof.
  induction tau => i' tau' Htau Htau'.

  + (* Init *)
    expand frame@init.
    have [Hinit | [j [HA1 HA2]]] := lastupdate_pure_glob i' tau' _; try auto.

    - use lastupdate_init with i',tau' as H; try auto.
      rewrite H //; expand s(i')@init. 
      by fresh 0.

    - use lastupdate_A with i',j,tau' as H; try auto.
      rewrite H // in *; expand s(i')@A(i',j).
      prf 0; [2: by fresh 0].
      simpl. intro j0 HAi0.
      use lastupdate with i',pred(A(i',j)) as [[H1 H2] | H1]; try auto.
        * use H2 with j0 as H3; try auto.
        * destruct H1 as [j1 [H1 H2 H3]].
          use monotonic_chain with pred(A(i',j)),pred(A(i',j0)),i',j1 => //.
          repeat split; try auto.
          use H3 with j0 as H4; try auto.

  + (* Oracle *)
     expand frame, exec, cond, output.
     fa !<_,_>, if _ then _, (_ && _), <_,_>.
     prf 1.
       * intro i0 j0 H.
         have ? : happens(pred (A(i0, j0))) by case H. 
         rewrite equiv IH i0 (pred(A(i0,j0))) => //. 
         intro Hf; by fresh Hf.
       * intro j0 H.
         by apply unique_queries.
       * intro i0 j0 H.
         have ? : happens(pred (A(i0, j0))) by auto. 
         rewrite equiv IH i0 (pred(A(i0,j0))) => //. 
         intro Hf; by fresh Hf.
       * fresh 1; 1:auto.
     prf 1. 
       simpl; split.
         ++ intro j0 H.
           apply unique_queries; auto.
         ++ intro i0 j0 H.
           rewrite equiv IH i0 (A(i0,j0)) => // Hf.
           by fresh Hf.
     fresh 1; 1:auto.
     by apply IH.

   + (* Tag *)
  expand frame@A(i,j). expand exec@A(i,j). expand cond@A(i,j). expand output@A(i,j).
  fa 0. fa 1. fa 1.
  prf 1.
    simpl; split.
      - intro j0 H.
        rewrite equiv IH i (A(i,j)) => // Hf; by fresh Hf.
      - intro i0 j0 H.
        assert i=i0 || i<>i0; try auto.
        case H0.
          * by use monotonic_chain with A(i,j),A(i,j0),i,j => //.
          * by use disjoint_chains with A(i,j),A(i0,j0),i,i0.
  fresh 1; 1:auto.
  by apply IH.
Qed.
