set autoIntro = false.

hash H
hash G
name k : message
name k' : message
name s0 : index -> message
mutable sT(i:index) : message = s0(i)
mutable sR(i:index) : message = s0(i)

abstract ok : message
channel cT
channel cR

process tag(i:index) =
  sT(i):=H(sT(i),k);
  out(cT,G(sT(i),k'))

process reader =
  in(cT,x); 
  try find ii such that x = G(H(sR(ii),k),k') in 
    sR(ii):=H(sR(ii),k); 
    out(cR,ok) 

system (!_i !_j T: tag(i) | !_jj R: reader).

goal lastupdate_pure_tag (i:index,tau:timestamp):
   happens(tau) => (
    (forall j:index, happens(T(i,j)) => T(i,j)>tau) ||
    (exists j:index, happens(T(i,j)) && T(i,j)<=tau && 
      forall j':index, happens(T(i,j')) && T(i,j')<=tau => T(i,j')<=T(i,j))).
Proof.
  induction tau => tau IH Hap.
  case tau.

  (* init *)
  by intro _; left.

  (* T(i0,j) *)
  intro [i0 j Eq]; subst tau, T(i0,j).
    (* 1st case: i<>i0 *)
    case (i<>i0) => //.
    intro Neq. 
    use IH with pred(T(i0,j)) => //.
    destruct H as [H1 | [j0 H2]].
      left; intro j0 HapT; by use H1 with j0.
      right; destruct H2 as [H21 H22]; exists j0.
      intro /= _ _.
      by apply H22.

    (* 2nd case: i<>i0 *)
    intro _; subst i0, i.
    by right; exists j.

  (* R(jj,ii) *)
  intro [jj ii Eq]; subst tau, R(jj,ii).
  use IH with pred(R(jj,ii)) => //.
  destruct H as [H1 | [j H2]].
    left; intro j HapT; by use H1 with j.

    right; destruct H2 as [H21 H22].
    exists j.
    intro /= _ _.
    by apply H22.

  (* R1(jj) *)
  intro [jj Eq]; subst tau, R1(jj).
  use IH with pred(R1(jj)) => //.
  destruct H as [H1 | [j H2]].
  left; intro j HapT; by use H1 with j.
    right; destruct H2 as [H21 H22].

    exists j.
    intro /= _ _.
    by apply H22.
Qed.


goal lastupdate_pure_reader (ii:index,tau:timestamp):
  happens(tau) => (
    (forall jj:index, happens(R(jj,ii)) => R(jj,ii)>tau) ||
    (exists jj:index, happens(R(jj,ii)) && R(jj,ii)<=tau && 
      forall jj':index, 
        happens(R(jj',ii)) && R(jj',ii)<=tau => R(jj',ii)<=R(jj,ii))).
Proof.
  induction tau => tau IH Hap.
  case tau.

  (* init *)
  by intro _; left.

  (* T(i,j) *)
  intro [i j Eq]; subst tau, T(i,j).
  use IH with pred(T(i,j)) => //.
  destruct H as [H1 | [jj H2]].
  left; intro jj HapR; by use H1 with jj => //.
    right; destruct H2 as [H21 H22].

    exists jj.
    intro /= _ _.
    by apply H22.

  (* R(jj,ii0) *)
  intro [jj ii0 Eq]; subst tau, R(jj,ii0).
    (* 1st case: ii<>ii0 *)
    case (ii<>ii0) => //.
    intro Neq.
    use IH with pred(R(jj,ii0)) => //.
    destruct H as [H1 | [jj0 H2]].
    left; intro jj0 HapR; by use H1 with jj0 => //.
    right; destruct H2 as [H21 H22]; exists jj0.
    split => //.
    intro jj'.
    intro Hyp.
    use H22 with jj' => //.
    (* 2nd case: ii<>ii0 *)
    intro Eq; subst ii0, ii.
    right; exists jj; split => //.

  (* R1(jj) *)
  intro [jj Eq]; subst tau, R1(jj).
  use IH with pred(R1(jj)) => //.
  destruct H as [H1 | [j H2]].
  left; intro j HapT; by use H1 with j => //.
  right. destruct H2 as [H21 H22].
  exists j.
  intro /= _ _.
  by apply H22.
Qed.

goal lastupdate_init_tag (i:index,tau:timestamp):
  happens(tau) => (
    (forall j:index, happens(T(i,j)) => T(i,j)>tau)) 
      => sT(i)@tau = sT(i)@init.
Proof.
  induction tau => tau IH Htau.
  case tau.

  (* init *)
  auto.

  (* T(i0,j) *)
  intro [i0 j HT]; rewrite HT in *.
  case (i = i0) => //.
    intro Eq H0.
    use H0 with j => //.

    intro Neq H0.
    use IH with pred(T(i0,j)) => //.
    expand sT.
    noif => //.
    intro j0.
    intro Hp.
    by use H0 with j0.

  (* R(jj,ii) *)
  intro HR. 
  repeat destruct HR as [_ HR]. 
  rewrite HR /sT in *.
  intro Hyp.
  apply IH => //.
  intro j _.
  by use Hyp with j.

  (* R1(jj) *)
  (* same proof script as above *)
  intro HR. 
  repeat destruct HR as [_ HR]. 
  rewrite HR /sT in *.
  intro Hyp.
  apply IH => //.
  intro j _.
  by use Hyp with j.
Qed.

goal lastupdate_init_reader (ii:index,tau:timestamp):
  happens(tau) => (
    (forall jj:index, happens(R(jj,ii)) => R(jj,ii)>tau)) 
      => sR(ii)@tau = sR(ii)@init.
Proof.
  induction tau => tau IH Htau.
  case tau.

  (* init *)
  auto.

  (* T(i,j) *)
  intro [i j HT]; rewrite HT in *.
  intro @/sR Hyp.
  use IH with pred(T(i,j)) => //.
  intro jj _.
  by use Hyp with jj.

  (* R(jj,ii0) *)
  intro [jj ii0 HR]; rewrite HR in *.
  case (ii = ii0) => //.
    intro Eq H0.
    by use H0 with jj.

    intro Neq H0.
    use IH with pred(R(jj,ii0)) => //.
    expand sR.
    noif => //.
    intro jj0 Hp.
    by use H0 with jj0.

  (* R1(jj) *)
  intro [jj HR1]; rewrite HR1 in *.
  intro @/sR Hyp.
  use IH with pred(R1(jj)) => //.
  intro jj0 _.
  by use Hyp with jj0.
Qed.

goal lastupdate_T (i:index, j:index, tau:timestamp):
    (happens(tau) && T(i,j)<=tau && 
      forall j':index, happens(T(i,j')) && T(i,j')<=tau => T(i,j')<=T(i,j))
    => sT(i)@tau = sT(i)@T(i,j).
Proof.
  induction tau => tau IH [Hp Ord Hyp].
  case tau.

  (* init *)
  auto.

  (* T(i0,j0) *)
  intro [i0 j0 H]; rewrite H in *.
  case (i=i0) => //.
    intro Eqi.
    use Hyp with j0 => //.
    by case (j=j0).

    intro Neqi.
    expand sT(i)@T(i0,j0).
    noif.
    auto.
    use IH with pred(T(i0,j0)) => //.
    intro /= _ _. 
    by apply Hyp.

  (* R(jj,ii) *)
  intro [jj ii HR]; rewrite HR in *.
  expand sT.
  use IH with pred(R(jj,ii)) => //.
  intro /= _ _. 
  by apply Hyp.

  (* R1(jj) *)
  intro [jj HR1]; rewrite HR1 in *.
  expand sT.
  use IH with pred(R1(jj)) => //.
  intro /= _ _. 
  by apply Hyp.
Qed.

goal lastupdate_R (ii:index, jj:index, tau:timestamp):
    (happens(tau) && R(jj,ii)<=tau && 
      forall jj':index, 
        happens(R(jj',ii)) && R(jj',ii)<=tau => R(jj',ii)<=R(jj,ii))
    => sR(ii)@tau = sR(ii)@R(jj,ii).
Proof.
  induction tau => tau IH [Hp Ord Hyp].
  case tau.

  (* init *)
  auto.

  (* T(i,j) *)
  intro [i j HT]; rewrite HT in *.
  expand sR.
  use IH with pred(T(i,j)) => //.
  intro /= _ _. 
  by apply Hyp.

  (* R(jj0,ii0) *)
  intro [jj0 ii0 H]; rewrite H in *.
  case (ii=ii0) => //.
    intro Eqii.
    use Hyp with jj0.
    case (jj=jj0) => //.
    auto.

    intro Neqii.
    expand sR.
    noif.
    auto.
    use IH with pred(R(jj0,ii0)) => //.
    intro /= _ _. 
    by apply Hyp.

  (* R1(jj0) *)
  intro [jj0 HR1]; rewrite HR1 in *.
  expand sR.
  use IH with pred(R1(jj0)) => //.
  intro /= _ _. 
  by apply Hyp.
Qed.

goal lastupdateTag (i:index,tau:timestamp):
  happens(tau) => (
    (sT(i)@tau = sT(i)@init && forall j:index, happens(T(i,j)) => T(i,j)>tau) ||
    (exists j:index, 
      sT(i)@tau = sT(i)@T(i,j) && T(i,j)<=tau && 
        forall j':index, happens(T(i,j')) && T(i,j')<=tau => T(i,j')<=T(i,j))).
Proof.
  intro Htau.
  use lastupdate_pure_tag with i, tau as [Hinit | [j [HTj1 HTj2 HTj3]]] => //.
    left. 
    simpl.
    by apply lastupdate_init_tag.
    
    right.
    exists j. 
    simpl.
    by apply lastupdate_T.
Qed.

goal lastupdateReader (ii:index,tau:timestamp):
  happens(tau) => (
    (sR(ii)@tau = sR(ii)@init && 
      forall jj:index, happens(R(jj,ii)) => R(jj,ii)>tau) ||
    (exists jj:index, 
      sR(ii)@tau = sR(ii)@R(jj,ii) && R(jj,ii)<=tau && 
        forall jj':index, 
          happens(R(jj',ii)) && R(jj',ii)<=tau => R(jj',ii)<=R(jj,ii))).
Proof.
  intro Htau.
  use lastupdate_pure_reader with ii, tau as [Hinit | [jj [HTj1 HTj2 HTj3]]] => //.
    left.  
    simpl.
    by apply lastupdate_init_reader.

    right.
    exists jj. 
    simpl.
    by apply lastupdate_R.
Qed.

goal disjoint_chains (tau',tau:timestamp,i',i:index) :
  happens(tau',tau) =>
    i<>i' => sT(i)@tau <> sR(i')@tau'.
Proof.
  generalize tau.
  induction tau' => tau' IH tau D E Meq.
  use lastupdateTag with i,tau as [[A0 Hinit] | [j [[A0 A1] Hsup]]] => //;
  use lastupdateReader with i',tau' as [[A Hinit'] | [j' [[B C] Hsup']]] => //.
  rewrite -Meq A0 /sR in B. 
  by fresh B.

  rewrite Meq A / sT in A0. 
  by fresh A0.

  rewrite Meq B / sT in A0.
  expand sR(i')@R(j',i').
  collision A0 => H.
  by use IH with pred(R(j',i')),pred(T(i,j)).
Qed.

goal authentication (jj,ii:index):
   happens(R(jj,ii)) =>
   cond@R(jj,ii) =>
   exists (j:index), T(ii,j) < R(jj,ii) && output@T(ii,j) = input@R(jj,ii).
Proof.
  intro Hap @/cond Hcond.  
  euf Hcond.
  intro Ht M.
  case (i=ii) => _; 1: by exists j.
  expand sT.
  collision.
  intro Meq.
  by use disjoint_chains with pred(R(jj,ii)),pred(T(i,j)),ii,i.
Qed.
