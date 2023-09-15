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

include Basic.

(** Last update lemmas: basic reasoning about the memory cell.
    Here we decompose the usual lastupdate lemma to separate the "pure" part
    from the part that involves message equalities. 
    The pure part is proven both as a local lemma and a global lemma. *)

lemma lastupdate_pure : forall tau,
  happens(tau) => (
    (forall j, happens(A(j)) => A(j)>tau) ||
    (exists i, happens(A(i)) && A(i) <=tau &&
     forall j, happens(A(j)) && A(j)<=tau => A(j)<=A(i))).
Proof.
  induction.
  intro tau IH Hp.
  case tau.
  
  (* init *)
  - intro Eq; left; intro j Hpj; by auto.
  
    (* O(i) *)
  - intro [i Eq]; subst tau, O(i); use IH with pred(O(i)) => //.
    destruct H as [H1 | [i0 H2]].
    + left; intro j Hpj; by use H1 with j => //.
    + right; exists i0; repeat split =>//.
      destruct H2 as [H21 H22 H23].
      intro j [Hpj Ord].
      case (A(j) <= pred( O(i))) => //.
      use H23 with j => //.
    
    (* A(i) *)
  - intro [i Eq]; subst tau, A(i); use IH with pred(A(i)) => //.
    destruct H as [H1 | [i0 H2]];
    try (right;
    exists i;
    repeat split => //).
Qed.

global lemma lastupdate_pure_glob :
  Forall (tau:timestamp[const]),
  [happens(tau)] -> (
    [forall (j:index), happens(A(j)) => A(j)>tau] \/
    (Exists (i:index[const]),
      [happens(A(i)) && A(i) <= tau] /\
      [forall (j:index), happens(A(j)) && A(j)<=tau => A(j)<=A(i)])).
Proof.
  dependent induction.
  intro tau IH Hp.
  case tau.

  (* init *)
  - intro Eq; left; intro j Hpj; by auto.
  
    (* O(i) *)
  - intro [i Eq]; rewrite Eq in *. 
    use IH with pred(O(i)) => //.
    destruct H as [H1 | [i0 H2]].
    + left; intro j Hpj; by use H1 with j => //.
    + destruct H2 as [[H21 H22] H23].
      right; exists i0. 
      repeat split =>//.
      intro j [Hpj Ord].
      case (A(j) <= pred( O(i))) => //.
      use H23 with j => //.
    
    (* A(i) *)
  - intro [i Eq]; rewrite Eq in *. 
    use IH with pred(A(i)) => //.
    destruct H as [H1 | [i0 H2]];
    try (right;
    exists i;
    repeat split => //).
Qed.

lemma lastupdate_init :
  forall tau,
  happens(tau) =>
  (forall j, happens(A(j)) => A(j)>tau) =>
  s@tau = s@init.
Proof.
  induction => tau IH _ Htau.
  case tau.

  - auto.

  - intro [i Hi]; rewrite Hi in *; expand s@O(i).
    apply IH => //.
    intro j Hp; by use Htau with j.
    
  - intro [i Hi]; rewrite Hi in *.
    by use Htau with i.
Qed.

lemma lastupdate_A :
  forall (tau:timestamp,i:index),
  happens(A(i)) && A(i)<=tau &&
  (forall j, happens(A(j)) && A(j)<=tau => A(j)<=A(i)) =>
  s@tau = s@A(i).
Proof.
  induction.
  intro tau IH i [Hap Hinf Hsup].

  case tau.

  - intro H; rewrite H in Hinf; auto.
    
  - intro [j Hj]; rewrite Hj in *; expand s@O(j).
    apply IH => //=.
    intro k Hk; by use Hsup with k.
    
  - intro [j Hj]; rewrite Hj in *.
    assert i=j; [2: auto | 1: by use Hsup with j].
Qed.

lemma lastupdate :
  forall tau,
  happens(tau) =>
    (s@tau = s@init && forall j, happens(A(j)) => A(j)>tau) ||
    (exists i, s@tau = s@A(i) &&
     happens(A(i)) && A(i)<=tau &&
     forall j, happens(A(j)) && A(j)<=tau => A(j)<=A(i)).
Proof.
  intro tau Htau.
  use lastupdate_pure with tau as [Hinit|[i HAi]] => //.
  left.
  split => //.
  by apply lastupdate_init.
  right; exists i; repeat split => //; by apply lastupdate_A.
Qed.


(** The contents of the memory cell never repeats. *)

lemma non_repeating :
  forall (beta,alpha:timestamp), happens(beta) =>
  (exists i, alpha < A(i) && A(i) <= beta) =>
  s@alpha <> s@beta.
Proof.
  induction => beta IH alpha _ [i [_ _]] Meq.
  use lastupdate with beta as [[_ Habs] | [j [_ _ _ Hsup]]] => //;
    1: by use Habs with i.

  use Hsup with i => //.
  (* We now have alpha < A(i) <= A(j) < beta
   * and no A(_) between A(j) and beta. *)

  assert s@alpha = s@A(j) as Meuf => //; expand s@A(j).
  euf Meuf => [i0 [Heuf _]].

  use IH with pred(A(j)),pred(A(i0)) => //.
  by case Heuf; exists i0.
Qed.


(** Strong secrecy *)

axiom unique_queries (i,j:index) : i <> j => input@O(i) <> input@O(j).

name m : message.

global lemma [set:default/left; equiv:default/left,default/left]
  strong_secrecy (tau:timestamp[const]) : 
    Forall (tau':timestamp[const]),
    [happens(tau)] -> [happens(tau')] -> equiv(frame@tau, diff(s@tau',m)).
Proof.
  induction tau => tau' Htau Htau'.

  (* Init *)
  - expand frame@init.
    have [Hinit | [i [[HA1 HA2] HA3]]] := lastupdate_pure_glob tau' _; 1:auto.    
    + have H := lastupdate_init tau' _ _; try auto. 
      rewrite H /s. 
      by fresh 0.
    
    + have H := lastupdate_A tau' i _=> //=. 
      rewrite H // in *; expand s@A(i). 
      prf 0; [2: by fresh 0].
      intro /= i' HAi'.
      use non_repeating with pred(A(i)),pred(A(i')) => //.
      by exists i'.
    
  (* Oracle *)
  - expand frame, output, exec, cond.
    fa 0; fa 1; fa 1; fa 1.

    
    prf 1.
    * intro i' H.
      have ? : happens(pred (A(i'))) by case H.
        rewrite equiv IH (pred(A(i'))) => //.
        intro Hf; by fresh Hf.
    * intro _ _. by apply unique_queries.
    * intro i' _.
      have ? : happens(pred (A(i'))) by auto.
        rewrite equiv IH (pred(A(i'))) => //.
        intro Hf; by fresh Hf.    
    * fresh 1; 1:auto.
      prf 1. 
      + split; intro i' H; try destruct H as [H|H];
        try by apply unique_queries.
        rewrite equiv IH (A(i')) => // Hf; by fresh Hf.
      + fresh 1; 1:auto.
        by apply IH.
    
  (* Tag *)
  - expand frame, exec, cond, output.
    fa 0; fa 1; fa 1.
    prf 1; 2: (fresh 1; [1: auto | 2: by apply IH]).
    split; intro i' H; try destruct H as [H|H].
    * rewrite equiv IH (A(i)) => // Hf; by fresh Hf.
    * use non_repeating with A(i),A(i') => //; by exists i.
Qed.
