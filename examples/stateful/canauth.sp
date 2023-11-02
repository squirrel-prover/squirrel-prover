(*******************************************************************************
CANAUTH

Vincent Cheval, Véronique Cortier, and Mathieu Turuani.
“A Little More Conversation, a Little Less Action, a Lot More Satisfaction:
Global States in ProVerif”.
CSF 2018.

Sender -> Receiver : <<msg,<SIGN,ctr>>,hmac(<ctr,msg>,sk)>
                     ctr := ctr+1
Receiver -> Sender : input x, check x
                     ctr := ctr+1

An agent has a cell which is used to store a counter.
This counter is incremented at each action (receive or send).

HELPING LEMMAS
- counter increase

SECURITY PROPERTIES
- authentication
- injectivity
*******************************************************************************)

hash hmac

name sk : index -> message
name msgA : index * index -> message
name msgB : index * index -> message

abstract SIGN : message
abstract myZero : message
abstract ok : message

mutable cellA(i:index) : message = myZero
mutable cellB(i:index) : message = myZero

channel cR
channel cS

(* mySucc function for counter *)
abstract mySucc : message -> message

(* order relation for counter *)
abstract (~<) : message -> message -> bool

(* PROCESSES *)

process ReceiverA(i,j:index) =
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellA(i) ~< snd(snd(fst(x)))
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(x))>,sk(i))
  then
    cellA(i) := mySucc(cellA(i));
    out(cS,ok)

process ReceiverB(i,j:index) =
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellB(i) ~< snd(snd(fst(x)))
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(x))>,sk(i))
  then
    cellB(i) := mySucc(cellB(i));
    out(cS,ok)

process SenderA(i,j:index) =
  cellA(i) := mySucc(cellA(i));
  out(cR,<<msgA(i,j),<SIGN,cellA(i)>>,hmac(<cellA(i),msgA(i,j)>,sk(i))>)

process SenderB(i,j:index) =
  cellB(i) := mySucc(cellB(i));
  out(cR,<<msgB(i,j),<SIGN,cellB(i)>>,hmac(<cellB(i),msgB(i,j)>,sk(i))>)

system ((!_i !_j ReceiverA(i,j)) | (!_i !_j SenderA(i,j)) |
        (!_i !_j ReceiverB(i,j)) | (!_i !_j SenderB(i,j))).


(* LIBRARIES *)

include Basic.

(* f_apply *)

lemma fst_apply (x,y : message) : x = y => fst(x) = fst(y).
Proof. auto. Qed.

lemma snd_apply (x,y : message) : x = y => snd(x) = snd(y).
Proof. auto. Qed.

(* AXIOMS *)

axiom orderSucc (n,n':message): n = n' => n ~< mySucc(n').

axiom orderTrans (n1,n2,n3:message): (n1 ~< n2 && n2 ~< n3) => n1 ~< n3.

axiom orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 => false.

axiom orderEqSucc (n1,n2:message):
  (n1 ~< mySucc(n2)) => ((n1 = n2) || n1 ~< n2).


(* HELPING LEMMAS *)

lemma orderBetween (n1,n2:message) :
 (n1 ~< n2) => (n2 ~< mySucc(n1)) => false.
Proof.
  intro Ord1 Ord2. 
  use orderEqSucc with n2, n1 => //.
  case H. 
    + by apply orderStrict in Ord1. 
    + use orderTrans with n1, n2, n1 => //. 
      by apply orderStrict in H0. 
Qed.


(* The counter cellA(i) strictly increases 
   at each action SenderA(i,j) / ReceiverA(i,j). *)

lemma counterIncreaseUpdateSA(i,j:index):
  happens(SenderA(i,j)) =>
  cond@SenderA(i,j) =>
  cellA(i)@pred(SenderA(i,j)) ~< cellA(i)@SenderA(i,j).
Proof.
  intro Hap Hcond @/cellA.
  by apply orderSucc.
Qed.

lemma counterIncreaseUpdateRA(i,j:index):
  happens(ReceiverA(i,j)) =>
  cond@ReceiverA(i,j) =>
  cellA(i)@pred(ReceiverA(i,j)) ~< cellA(i)@ReceiverA(i,j).
Proof.
  intro Hap Hcond @/cellA.
  by apply orderSucc.
Qed.


(* The counter cellB(i) strictly increases
   at each action SenderB(i,j) / ReceiveB(i,j). *)

lemma counterIncreaseUpdateSB(i,j:index):
  happens(SenderB(i,j)) =>
  cond@SenderB(i,j) =>
  cellB(i)@pred(SenderB(i,j)) ~< cellB(i)@SenderB(i,j).
Proof.
  intro Hap Hcond @/cellB.
  by apply orderSucc. 
Qed.

lemma counterIncreaseUpdateRB(i,j:index):
  happens(ReceiverB(i,j)) =>
  cond@ReceiverB(i,j) =>
  cellB(i)@pred(ReceiverB(i,j)) ~< cellB(i)@ReceiverB(i,j).
Proof.
  intro Hap Hcond @/cellB.
  by apply orderSucc. 
Qed.


(* The counter cellB(i) at t is either equal to cellB(i)@pred(t) or +1,
   and similarly for cellA(i). *)

lemma ScounterIncreasePredB(t:timestamp, i:index):
  happens(t) =>
  t > init =>
  exec@t =>
  (cellB(i)@t = mySucc(cellB(i)@pred(t)) || cellB(i)@t= cellB(i)@pred(t)).
Proof.
  intro Hap Ht Hexec.
  case t => // [i0 j _]. 
    (* Receiver *)
    + case (i = i0) => _. 
      - left.
        by rewrite /cellB if_true. 
      - right. 
        by rewrite /cellB if_false. 
    (* Sender *) 
    + case (i = i0) => _. 
      - left. 
        by rewrite /cellB if_true. 
      - right. 
        by rewrite /cellB if_false. 
Qed.


lemma ScounterIncreasePredA(t:timestamp, i:index):
  happens(t) =>
  t > init =>
  exec@t =>
  (cellA(i)@t = mySucc(cellA(i)@pred(t)) || cellA(i)@t= cellA(i)@pred(t)).
Proof.
  intro Hap Ht Hexec.
  case t => // [i0 j _].
  (* Receiver *)
    + case (i = i0) => _.
      - left.
        by rewrite /cellA if_true. 
      - right. 
        by rewrite /cellA if_false. 
  (* Sender *)
    + case (i = i0) => _.
      - left. 
        by rewrite /cellA if_true. 
      - right. 
        by rewrite /cellA if_false. 
Qed.


(* The counter increases (not strictly) between t and pred(t). *)

lemma counterIncreasePredA(t:timestamp, i:index):
  happens(t) => (t > init && exec@t) =>
    ( cellA(i)@pred(t) ~< cellA(i)@t
      || cellA(i)@pred(t) = cellA(i)@t ).
Proof.
  intro Hap [Ht Hexec].
  use ScounterIncreasePredA with t, i => //.
  case H.
    + by left; rewrite H; apply orderSucc.
    + by right.
Qed.


lemma counterIncreasePredB(t:timestamp, i:index):
  happens(t) => (t > init && exec@t) =>
    ( cellB(i)@pred(t) ~< cellB(i)@t
      || cellB(i)@pred(t) = cellB(i)@t ).
Proof.
  intro Hap [Ht Hexec].
     use ScounterIncreasePredB with t, i => //. 
     case H. 
       + by left; rewrite H; apply orderSucc.
       + by right. 
Qed.

(* The counter increases (not strictly) between t' and t when t' < t. *)

lemma counterIncreaseA (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellA(i)@t' ~< cellA(i)@t ||
    cellA(i)@t' = cellA(i)@t).
Proof.
  induction t => t IH0 Hap Hexec Ht'.
  assert (t' = pred(t) || t' < pred(t)) as H0;
  1: case t; constraints.
  case H0.

    + (* case t' = pred(t) *)
      rewrite !H0.
      by apply counterIncreasePredA.

     + (* case t' < pred(t) *)
       apply IH0 in H0 => //=.
         - executable t => // H1; by apply H1.
         - use counterIncreasePredA with t,i as H3 => //.
           case H0.
           *  by case H3;
              [1: left; apply orderTrans _ (cellA(i)@pred(t)) _ |
               2: rewrite H3 in H0; left].

           * rewrite H0.
             by case H3; [1: left | 2 : right].
Qed.


lemma counterIncreaseB (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellB(i)@t' ~< cellB(i)@t ||
    cellB(i)@t' = cellB(i)@t).
Proof.
  induction t => t IH0 Hap Hexec Ht'.
  assert (t' = pred(t) || t' < pred(t)) as H0;
  1: case t; constraints.
  case H0.
    + (* case t' = pred(t) *)
      rewrite !H0.
      by apply counterIncreasePredB.

    + (* case t' < pred(t) *)
      apply IH0 in H0 => //=.
        - executable t => // H1; by apply H1.
        - use counterIncreasePredB with t,i as H3 => //. case H0.
          *  by case H3;
             [1: left; apply orderTrans _ (cellB(i)@pred(t)) _ |
              2: rewrite H3 in H0; left].
          * rewrite H0. by case H3; [1: left | 2 : right].
Qed.


(* The counter cellA(i) strictly increases between t and t'
   when t < t' and (t' = SenderA(i,j1) or t' = ReceiverA(i,j1)). *)

lemma counterIncreaseStrictSA(i,j1:index, t:timestamp):
  happens(SenderA(i,j1)) =>
    (t < SenderA(i,j1) && exec@SenderA(i,j1)) =>
      cellA(i)@t ~< cellA(i)@SenderA(i,j1).
Proof.
 intro Hap [Ht Hexec].
 use counterIncreaseUpdateSA with i,j1 as Meq => //.
 assert (
   t < pred(SenderA(i,j1))
   || t = pred(SenderA(i,j1))) as H => //.

 case H; 2: by rewrite H.
 use counterIncreaseA with pred(SenderA(i,j1)),t,i as H0 => //.
 case H0; 2: by rewrite H0.
 by apply orderTrans _ (cellA(i)@pred(SenderA(i,j1))).
Qed.

lemma counterIncreaseStrictRA (i,j1:index, t:timestamp):
  happens(ReceiverA(i,j1)) =>
    (t < ReceiverA(i,j1) && exec@ReceiverA(i,j1)) =>
      cellA(i)@t ~< cellA(i)@ReceiverA(i,j1).
Proof.
 intro Hap [Ht Hexec].
  use counterIncreaseUpdateRA with i,j1 as Meq => //.
  assert (
    t < pred(ReceiverA(i,j1))
    || t = pred(ReceiverA(i,j1))) as H => //.

  case H; 2: by rewrite H.
  use counterIncreaseA with pred(ReceiverA(i,j1)),t,i as H0 => //.
  case H0; 2: by rewrite H0.
  by apply orderTrans _ (cellA(i)@pred(ReceiverA(i,j1))).
Qed.

(* The counter cellB(i) strictly increases between t and t'
   when t < t' and (t' = SenderB(i,j1) or t' = ReceiverB(i,j1)). *)

lemma counterIncreaseStrictSB (i,j1:index, t:timestamp):
  happens(SenderB(i,j1)) =>
    (t < SenderB(i,j1) && exec@SenderB(i,j1)) =>
      cellB(i)@t ~< cellB(i)@SenderB(i,j1).
Proof.
 intro Hap [Ht Hexec].
 use counterIncreaseUpdateSB with i,j1 as Meq => //.
 assert (
   t < pred(SenderB(i,j1))
   || t = pred(SenderB(i,j1))) as H => //.

 case H; 2: by rewrite H.
 use counterIncreaseB with pred(SenderB(i,j1)),t,i as H0 => //.
 case H0; 2: by rewrite H0.
 by apply orderTrans _ (cellB(i)@pred(SenderB(i,j1))).
Qed.

lemma counterIncreaseStrictRB (i,j1:index, t:timestamp):
  happens(ReceiverB(i,j1)) =>
    (t < ReceiverB(i,j1) && exec@ReceiverB(i,j1)) =>
      cellB(i)@t ~< cellB(i)@ReceiverB(i,j1).
Proof.
 intro Hap [Ht Hexec].
 use counterIncreaseUpdateRB with i,j1 as Meq => //.
 assert (
   t < pred(ReceiverB(i,j1))
   || t = pred(ReceiverB(i,j1))) as H => //.

 case H; 2: by rewrite H.
 use counterIncreaseB with pred(ReceiverB(i,j1)),t,i as H0 => //.
 case H0; 2: by rewrite H0.
 by apply orderTrans _ (cellB(i)@pred(ReceiverB(i,j1))).
Qed.




(* SECURITY PROPERTIES *)

(* 1st property w.r.t. A *)
(* This security property is actually stronger than the one stated in
   the GSVerif paper. The send action has been done by agent B, and we
   also proved a lemma regarding counters.
   Moreover, we use this 1st property (authentication) to prove the
   2nd property (injectivity). *)


lemma authA (i,j:index) :
  happens(ReceiverA(i,j)) => exec@ReceiverA(i,j) =>
  (exists (j':index),
    SenderB(i,j') < ReceiverA(i,j)
    && snd(output@SenderB(i,j')) = snd(input@ReceiverA(i,j))
    && fst(fst(output@SenderB(i,j'))) = fst(fst(input@ReceiverA(i,j)))
    && snd(snd(fst(output@SenderB(i,j')))) = snd(snd(fst(input@ReceiverA(i,j))))
    && cellA(i)@pred(ReceiverA(i,j)) ~< cellB(i)@SenderB(i,j')).
Proof.
  intro Hap @/exec @/cond [Hexecpred [H1 H2 H3]].
  euf H3.
    + intro [j0 [H4 [H5 _]]].
      rewrite H5 in H2.
      use counterIncreaseStrictRA with i,j, SenderA(i,j0) as Hyp => //.
      expand cellA(i)@ReceiverA(i,j).
      by apply orderBetween in H2.

    + intro [j0 [H4 [H5 _]]].
      exists j0.
      rewrite H5 in H2.
      auto.
Qed.


(* 1st property w.r.t. B *)
lemma authB(i,j:index) :
  happens(ReceiverB(i,j)) => exec@ReceiverB(i,j) =>
  (exists (j':index),
     SenderA(i,j') < ReceiverB(i,j)
     && snd(output@SenderA(i,j')) = snd(input@ReceiverB(i,j))
     && fst(fst(output@SenderA(i,j'))) = fst(fst(input@ReceiverB(i,j)))
     && snd(snd(fst(output@SenderA(i,j')))) = snd(snd(fst(input@ReceiverB(i,j))))
     && cellB(i)@pred(ReceiverB(i,j)) ~< cellA(i)@SenderA(i,j')).
Proof.
  intro Hap @/exec @/cond [Hexecpred [H1 H2 H3]].
  euf H3.
  + intro [j0 [H4 [H5 _]]].
    exists j0.
   rewrite H5 in H2.
    auto.

  + intro [j0 [H4 [H5 _]]].
    rewrite H5 in H2.
    use counterIncreaseStrictRB with i,j, SenderB(i,j0) as Hyp => //.
    expand cellB(i)@ReceiverB(i,j).
    by apply orderBetween in H2.
Qed.


(* 2nd property w.r.t A and A *)
lemma injectivity(i,j,j':index) :
  happens(ReceiverA(i,j)) && happens(ReceiverA(i,j')) =>
  exec@ReceiverA(i,j) && exec@ReceiverA(i,j') =>
  (fst(fst(input@ReceiverA(i,j))) = fst(fst(input@ReceiverA(i,j')))
   && snd(snd(fst(input@ReceiverA(i,j)))) = snd(snd(fst(input@ReceiverA(i,j')))))
  ||
  (fst(fst(input@ReceiverA(i,j))) <> fst(fst(input@ReceiverA(i,j')))
   && snd(snd(fst(input@ReceiverA(i,j)))) <> snd(snd(fst(input@ReceiverA(i,j'))))).



Proof.
  intro [Hap Hap'] [Hexec Hexec'].
  use authA with i,j as H => //.
  destruct H as [j1 [Ord Eq0  Eq1 Eq2 HCpt]].
  use authA with i,j' as H => //.
  destruct H as [j1' [Ord' Eq0' Eq1' Eq2' HCpt']].
  expand output.
  simpl.

  case (j1 = j1') => H.
    + by left.
    + right.
      split;
      1: by rewrite -Eq1 -Eq1' in *.
      rewrite -Eq2 -Eq2' in *.
      assert (SenderB(i,j1) < SenderB(i,j1') ||
              SenderB(i,j1') < SenderB(i,j1)) as H0 by auto.
      case H0.
   
        (* SenderB(i,j1) < SenderB(i,j1') *)
        - use counterIncreaseStrictSB with i, j1', SenderB(i,j1) => //=.
          intro U; by apply orderStrict in U.
          executable ReceiverA(i,j') => // HexecPred'.
          by apply HexecPred'.

        (* SenderB(i,j1') < SenderB(i,j1) *)
        - use counterIncreaseStrictSB with i, j1, SenderB(i,j1') => //=.
           * intro U. rewrite eq_sym in U; by apply orderStrict in U.
           * executable ReceiverA(i,j) => // HexecPred. by apply HexecPred.
Qed.


(* 2nd property w.r.t A and B *)
lemma injectivityAB(i,j,j':index) :
  happens(ReceiverA(i,j)) && happens(ReceiverB(i,j')) =>
  exec@ReceiverA(i,j) && exec@ReceiverB(i,j') =>
  (fst(fst(input@ReceiverA(i,j))) = fst(fst(input@ReceiverB(i,j')))
   && snd(snd(fst(input@ReceiverA(i,j)))) = snd(snd(fst(input@ReceiverB(i,j')))))
  ||
  (fst(fst(input@ReceiverA(i,j))) <> fst(fst(input@ReceiverB(i,j')))
   && snd(snd(fst(input@ReceiverA(i,j)))) <> snd(snd(fst(input@ReceiverB(i,j'))))).

Proof.
  intro [Hap Hap'] [Hexec Hexec'].
  use authA with i,j as H => //.
  destruct H as [j1 [Ord Eq0 Eq1 Eq2 HCpt]].
  use authB with i,j' as H => //.
  destruct H as [j1' [Ord' Eq0' Eq1' Eq2' HCpt']].
  expand output.
  simpl.

  rewrite -Eq1 -Eq1' -Eq2 -Eq2' in *.

  right.
  split => //.

  assert (SenderB(i,j1) < ReceiverB(i,j') ||
          ReceiverB(i,j') < SenderB(i,j1)) as H by auto.
  case H.

    + (* SenderB(i,j1) < ReceiverB(i,j') *)
      use counterIncreaseStrictRB with i, j',SenderB(i,j1) as Meq => //.
      expand cellB(i)@ReceiverB(i,j').
      apply orderEqSucc in Meq.
      case Meq.
 
      - rewrite -Meq in HCpt'.
        intro U.
        by apply orderStrict in U.

      - use orderTrans with cellB(i)@SenderB(i,j1), cellB(i)@pred(ReceiverB(i,j')), cellA(i)@SenderA(i,j1') => //.
        by intro U; apply orderStrict in U.

    + (* ReceiverB(i,j') <  SenderB(i,j1) *)
      assert (SenderA(i,j1') <ReceiverA(i,j) || ReceiverA(i,j) <SenderA(i,j1')) as H0 by auto.
      case H0.

       - (* SenderA(i,j1') < ReceiverA(i,j) *)
         use counterIncreaseStrictRA with i, j,SenderA(i,j1') as Meq => //.
         expand cellA(i)@ReceiverA(i,j).
         apply orderEqSucc in Meq.
         case Meq.
    
           * rewrite -Meq in HCpt. intro U. rewrite eq_sym in U. by apply orderStrict in U.
           * use orderTrans with cellA(i)@SenderA(i,j1'), cellA(i)@pred(ReceiverA(i,j)), cellB(i)@SenderB(i,j1) => //.
             intro U.
             rewrite eq_sym in U.
             by apply orderStrict in U.

       - (* ReceiverA(i,j) < SenderA(i,j1') *)
         (* We have SendB < ReceiveA < SendA < ReceiveB < SendB ==> contradiction *)
          auto.
Qed.


(* 2nd property w.r.t. B and B *)
(* Similar to the case w.r.t. A and A *)
