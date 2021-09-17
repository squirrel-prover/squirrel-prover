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

An agent has a cell which is used to strore a counter. This counter is incremented at each action (receive or send).

PROOFS
- authentication
- injectivity
*******************************************************************************)

set autoIntro = false.

hash hmac

name sk : index -> message
name msgA : index -> index -> message
name msgB : index -> index -> message

abstract SIGN : message
abstract myZero : message
abstract ok : message

mutable cellA(i:index) : message = myZero
mutable cellB(i:index) : message = myZero

channel cR
channel cS

(* mySucc function for counter *)
abstract mySucc : message->message

(* order relation for counter *)
abstract orderOk : message
abstract (~<) : message->message->message

(* PROCESSES *)

process ReceiverA(i,j:index) =
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellA(i) ~< snd(snd(fst(x))) = orderOk
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(x))>,sk(i))
  then 
    cellA(i) := mySucc(cellA(i));
    out(cS,ok)

process ReceiverB(i,j:index) =
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellB(i) ~< snd(snd(fst(x))) = orderOk
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
(* A inclure dans une lib standard *)

goal eq_sym ['a] (x,y : 'a) : x = y => y = x.
Proof. auto. Qed.

goal if_false ['a] (b : boolean, x,y : 'a):
 (not b) => if b then x else y = y.
Proof.
 by intro *; noif. 
Qed.

goal if_true ['a] (b : boolean, x,y : 'a):
 b => if b then x else y = x.
Proof.
  by intro *; yesif.
Qed.

goal if_true0 ['a] (x,y : 'a):
 if true then x else y = x.
Proof.
  by rewrite if_true. 
Qed.
hint rewrite if_true0.

goal if_false0 ['a] (x,y : 'a):
 if false then x else y = y.
Proof.
  by rewrite if_false.
Qed.
hint rewrite if_false0.

goal fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.
hint rewrite fst_pair.

goal snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.
hint rewrite snd_pair.

(* f_apply *)

goal fst_apply (x,y : message) : x = y => fst(x) = fst(y).
Proof. auto. Qed.

goal snd_apply (x,y : message) : x = y => snd(x) = snd(y).
Proof. auto. Qed.

(* AXIOMS *)

axiom orderSucc (n:message): n ~< mySucc(n) = orderOk

axiom orderTrans  (n1,n2,n3:message): (n1 ~< n2 = orderOk && n2 ~< n3 = orderOk) => n1 ~< n3 = orderOk

axiom orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 <> orderOk.

axiom orderEqSucc (n1,n2:message): (n1 ~< mySucc(n2) =orderOk) => ((n1 = n2) || n1 ~< n2 = orderOk).

(** HELPING LEMMAS *)

goal orderBetween (n1,n2:message) :
 (n1 ~< n2 = orderOk) && (n2 ~< mySucc(n1) = orderOk) => false.
Proof.
intro [Ord1 Ord2].
use orderEqSucc with n2, n1.
case H.
use orderStrict with n2, n1; by auto.
use orderTrans with n1, n2, n1 => //.
use orderStrict with n1, n1; by auto.
by auto.
Qed.
 

(* The counter cellA(i) strictly increases at each action SenderA(i,j) / ReceiveA(i,j). *)

goal counterIncreaseUpdateSA(i,j:index): 
  happens(SenderA(i,j)) => cond@SenderA(i,j) =>
    cellA(i)@pred(SenderA(i,j)) ~< cellA(i)@SenderA(i,j) = orderOk.
Proof.
  intro Hap Hcond.  
  use orderSucc with cellA(i)@pred(SenderA(i,j)).
  expand cellA.  
  assumption.
Qed.

goal counterIncreaseUpdateRA(i,j:index): 
  happens(ReceiverA(i,j)) => cond@ReceiverA(i,j) =>
    cellA(i)@pred(ReceiverA(i,j)) ~< cellA(i)@ReceiverA(i,j) = orderOk.
Proof.
  intro Hap Hcond.  
  use orderSucc with cellA(i)@pred(ReceiverA(i,j)).
  expand cellA.  
  assumption.
Qed.


(* The counter cellB(i) strictly increases at each action SenderB(i,j) / ReceiveB(i,j). *)

goal counterIncreaseUpdateSB(i,j:index): 
  happens(SenderB(i,j)) => cond@SenderB(i,j) =>
    cellB(i)@pred(SenderB(i,j)) ~< cellB(i)@SenderB(i,j) = orderOk.
Proof.
  intro Hap Hcond.  
  use orderSucc with cellB(i)@pred(SenderB(i,j)).
  expand cellB.  
  assumption.
Qed.

goal counterIncreaseUpdateRB(i,j:index): 
  happens(ReceiverB(i,j)) => cond@ReceiverB(i,j) =>
    cellB(i)@pred(ReceiverB(i,j)) ~< cellB(i)@ReceiverB(i,j) = orderOk.
Proof.
  intro Hap Hcond.  
  use orderSucc with cellB(i)@pred(ReceiverB(i,j)).
  expand cellB.  
  assumption.
Qed.



(* The counter cellB(i)/cellA(i) at t is either equal to cellB(i)@pred(t) or +1 *)


goal ScounterIncreasePredB(t:timestamp, i:index): 
  happens(t) => (t > init && exec@t) =>
    (  cellB(i)@t = mySucc(cellB(i)@pred(t))
      || cellB(i)@t= cellB(i)@pred(t)   ).
Proof.
  intro Hap [Ht Hexec].  
  case t => //.

  intro [i0 j _].
  case (i = i0) => _.
    (* i = i0 *)
    left.
    use orderSucc with cellB(i)@pred(t).
    expand cellB.  
   auto.
    (* i <> i0 *)
    right.
    by rewrite /cellB if_false.

  (* Sender *)
 intro [i0 j _].
  case (i = i0) => _.
    (* i = i0 *)
    left.
    use orderSucc with cellB(i)@pred(t).
    expand cellB.  
auto.
    (* i <> i0 *)
    right.
    by rewrite /cellB if_false.
Qed.


goal ScounterIncreasePredA(t:timestamp, i:index): 
  happens(t) => (t > init && exec@t) =>
    (  cellA(i)@t = mySucc(cellA(i)@pred(t))
      || cellA(i)@t= cellA(i)@pred(t)   ).
Proof.
  intro Hap [Ht Hexec].  
  case t => //.

  intro [i0 j _].
  case (i = i0) => _.
    (* i = i0 *)
    left.
    use orderSucc with cellA(i)@pred(t).
    expand cellA.  
   auto.
    (* i <> i0 *)
    right.
    by rewrite /cellA if_false.

  (* Sender *)
 intro [i0 j _].
  case (i = i0) => _.
    (* i = i0 *)
    left.
    use orderSucc with cellA(i)@pred(t).
    expand cellA.  
auto.
    (* i <> i0 *)
    right.
    by rewrite /cellA if_false.
Qed.


(* The counter cellA(i)/cellB(i) increases (not strictly) between t and pred(t) *)


goal counterIncreasePredA(t:timestamp, i:index): 
  happens(t) => (t > init && exec@t) =>
    ( cellA(i)@pred(t) ~< cellA(i)@t = orderOk
      || cellA(i)@pred(t) = cellA(i)@t ).
Proof.
  intro Hap [Ht Hexec].  
  use ScounterIncreasePredA with t, i => //.
  case H.
  left; use orderSucc with cellA(i)@pred(t); by auto.
  right; by auto.
Qed.




goal counterIncreasePredB(t:timestamp, i:index): 
  happens(t) => (t > init && exec@t) =>
    ( cellB(i)@pred(t) ~< cellB(i)@t = orderOk
      || cellB(i)@pred(t) = cellB(i)@t ).
Proof.
  intro Hap [Ht Hexec].  
  use ScounterIncreasePredB with t, i => //.
  case H.
  left; use orderSucc with cellB(i)@pred(t); by auto.
  right; by auto.
Qed.



(* The counter cellA(i)/CellB(i) increases (not strictly) between t' and t when t' < t. *)

goal counterIncreaseA:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
    exec@t && t' < t =>
    ( cellA(i)@t' ~< cellA(i)@t = orderOk || 
      cellA(i)@t' = cellA(i)@t).
Proof.
  induction.
  intro t IH0 t' i Hap [Hexec Ht'].
  assert (t' = pred(t) || t' < pred(t)) as H0; 
  1: case t; constraints. 
  case H0.

  (* case t' = pred(t) *)
  rewrite !H0. 
  by apply counterIncreasePredA.

  (* case t' < pred(t) *)
  use IH0 with pred(t),t',i as H1 => //.
  use counterIncreasePredA with t,i as H3 => //.
  case H1 => //.
    (* case H1 - 1/2 *)
    case H3 => //.
      by left; apply orderTrans _ (cellA(i)@pred(t)) _.
      (* case H1 - 2/2 *)
      by case H3; [1: left | 2 : right].
  
      simpl.
      executable t => // H1. 
      by apply H1.
Qed.

goal counterIncreaseB:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
    exec@t && t' < t =>
    ( cellB(i)@t' ~< cellB(i)@t = orderOk || 
      cellB(i)@t' = cellB(i)@t).
Proof.
  induction.
  intro t IH0 t' i Hap [Hexec Ht'].
  assert (t' = pred(t) || t' < pred(t)) as H0; 
  1: case t; constraints. 
  case H0.

  (* case t' = pred(t) *)
  rewrite !H0. 
  by apply counterIncreasePredB.

  (* case t' < pred(t) *)
  use IH0 with pred(t),t',i as H1 => //.
  use counterIncreasePredB with t,i as H3 => //.
  case H1 => //.
    (* case H1 - 1/2 *)
    case H3 => //.
      by left; apply orderTrans _ (cellB(i)@pred(t)) _.
      (* case H1 - 2/2 *)
      by case H3; [1: left | 2 : right].
  
      simpl.
      executable t => // H1. 
      by apply H1.
Qed.



(* The counter cellA(i) strictly increases between t and t'  
when t < t' and (t' = SenderA(i,j1) or t' = ReceiverA(i,j1)). *)


goal counterIncreaseStrictSA(i,j1:index, t:timestamp): 
  happens(SenderA(i,j1)) => 
    (t < SenderA(i,j1) && exec@SenderA(i,j1)) =>
      cellA(i)@t ~< cellA(i)@SenderA(i,j1) = orderOk.
Proof.
 intro Hap [Ht Hexec].  
  use counterIncreaseUpdateSA with i,j1 => //.
  assert (
    t < pred(SenderA(i,j1))
    || t = pred(SenderA(i,j1))) as H => //.
  case H => //.
    use counterIncreaseA with pred(SenderA(i,j1)),t,i as H0 => //.
    case H0 => //.
      use orderTrans with
        cellA(i)@t,
        cellA(i)@pred(SenderA(i,j1)),
        cellA(i)@SenderA(i,j1) => //.
Qed.


goal counterIncreaseStrictRA(i,j1:index, t:timestamp): 
  happens(ReceiverA(i,j1)) => 
    (t < ReceiverA(i,j1) && exec@ReceiverA(i,j1)) =>
      cellA(i)@t ~< cellA(i)@ReceiverA(i,j1) = orderOk.
Proof.
  intro Hap [Ht Hexec].  
  use counterIncreaseUpdateRA with i,j1 => //.
  assert (
    t < pred(ReceiverA(i,j1))
    || t = pred(ReceiverA(i,j1))) as H => //.
  case H => //.
    use counterIncreaseA with pred(ReceiverA(i,j1)),t,i as H0 => //.
    case H0 => //.
      use orderTrans with
        cellA(i)@t,
        cellA(i)@pred(ReceiverA(i,j1)),
        cellA(i)@ReceiverA(i,j1) => //.
Qed.


(* The counter cellB(i) strictly increases between t and t'  
when t < t' and (t' = SenderB(i,j1) or t' = ReceiverB(i,j1)). *)


goal counterIncreaseStrictSB(i,j1:index, t:timestamp): 
  happens(SenderB(i,j1)) => 
    (t < SenderB(i,j1) && exec@SenderB(i,j1)) =>
      cellB(i)@t ~< cellB(i)@SenderB(i,j1) = orderOk.
Proof.
 intro Hap [Ht Hexec].  
  use counterIncreaseUpdateSB with i,j1 => //.
  assert (
    t < pred(SenderB(i,j1))
    || t = pred(SenderB(i,j1))) as H => //.
  case H => //.
    use counterIncreaseB with pred(SenderB(i,j1)),t,i as H0 => //.
    case H0 => //.
      use orderTrans with
        cellB(i)@t,
        cellB(i)@pred(SenderB(i,j1)),
        cellB(i)@SenderB(i,j1) => //.
Qed.



goal counterIncreaseStrictRB(i,j1:index, t:timestamp): 
  happens(ReceiverB(i,j1)) => 
    (t < ReceiverB(i,j1) && exec@ReceiverB(i,j1)) =>
      cellB(i)@t ~< cellB(i)@ReceiverB(i,j1) = orderOk.
Proof.
  intro Hap [Ht Hexec].  
  use counterIncreaseUpdateRB with i,j1 => //.
  assert (
    t < pred(ReceiverB(i,j1))
    || t = pred(ReceiverB(i,j1))) as H => //.
  case H => //.
    use counterIncreaseB with pred(ReceiverB(i,j1)),t,i as H0 => //.
    case H0 => //.
      use orderTrans with
        cellB(i)@t,
        cellB(i)@pred(ReceiverB(i,j1)),
        cellB(i)@ReceiverB(i,j1) => //.
Qed.


(* GOALS *)

(* 1st property w.r.t. A *)
(* This security property is actually stronger than the  one stated in the GSVerif paper.
The send action has been done by agent B, and we also proved a property regarding counters. 
This extra property is used to prove the other  property. *)

goal authA(i,j:index) :
  happens(ReceiverA(i,j)) => exec@ReceiverA(i,j) => 
(
    exists (j':index), 
      SenderB(i,j') < ReceiverA(i,j) 
      && snd(output@SenderB(i,j')) = snd(input@ReceiverA(i,j))
      && fst(fst(output@SenderB(i,j'))) = fst(fst(input@ReceiverA(i,j)))
      && snd(snd(fst(output@SenderB(i,j')))) = snd(snd(fst(input@ReceiverA(i,j))))
      && cellA(i)@pred(ReceiverA(i,j)) ~< cellB(i)@SenderB(i,j') = orderOk
).
Proof.
  intro Hap Hexec.
  expand exec. destruct Hexec as [Hexecpred Hcond]. expand cond.
  destruct Hcond as [H1 H2 H3].
  euf H3.

  intro H4 H5 _.
  assert(cellA(i)@pred(ReceiverA(i,j)) ~< cellA(i)@SenderA(i,j0) = orderOk) => //.
  use counterIncreaseStrictRA with i,j, SenderA(i,j0) as Hyp => //.
  expand cellA(i)@ReceiverA(i,j).
  use orderBetween with cellA(i)@pred(ReceiverA(i,j)), cellA(i)@SenderA(i,j0) => //.

  intro H4 H5 _.   
  exists j0.  
  repeat split => //.
Qed.

(* 1st property w.r.t. B *)
goal authB(i,j:index) :
  happens(ReceiverB(i,j)) => exec@ReceiverB(i,j) => 
(
    exists (j':index), 
      SenderA(i,j') < ReceiverB(i,j) 
      && snd(output@SenderA(i,j')) = snd(input@ReceiverB(i,j))
      && fst(fst(output@SenderA(i,j'))) = fst(fst(input@ReceiverB(i,j)))
      && snd(snd(fst(output@SenderA(i,j')))) = snd(snd(fst(input@ReceiverB(i,j))))
      && cellB(i)@pred(ReceiverB(i,j)) ~< cellA(i)@SenderA(i,j') = orderOk 
).
Proof.
  intro Hap Hexec.
  expand exec. destruct Hexec as [Hexecpred Hcond]. expand cond.
  destruct Hcond as [H1 H2 H3].
  euf H3.

  intro H4 H5 _.
  exists j0. 
  repeat split => //. 

  intro H4 H5 _.   
  assert(cellB(i)@pred(ReceiverB(i,j)) ~< cellB(i)@SenderB(i,j0) = orderOk) => //.
  use counterIncreaseStrictRB with i,j, SenderB(i,j0) as Hyp => //.
  expand cellB(i)@ReceiverB(i,j).
  use orderBetween with cellB(i)@pred(ReceiverB(i,j)), cellB(i)@SenderB(i,j0) => //.
Qed.


(* 2nd property w.r.t A and A *)
goal injectivity(i,j,j':index) :
  happens(ReceiverA(i,j)) && happens(ReceiverA(i,j')) =>
    exec@ReceiverA(i,j) && exec@ReceiverA(i,j') => 
      (fst(fst(input@ReceiverA(i,j))) = fst(fst(input@ReceiverA(i,j')))
      && snd(snd(fst(input@ReceiverA(i,j)))) = snd(snd(fst(input@ReceiverA(i,j')))))
      ||
      (fst(fst(input@ReceiverA(i,j))) <> fst(fst(input@ReceiverA(i,j')))
      && snd(snd(fst(input@ReceiverA(i,j)))) <> snd(snd(fst(input@ReceiverA(i,j'))))).

Proof.
  intro [Hap Hap'] [Hexec Hexec'].
    use authA with i,j => //. destruct H as [j1 [Ord Eq0  Eq1 Eq2 HCpt]].
    use authA with i,j' => //.destruct H as [j1' [Ord' Eq0' Eq1' Eq2' HCpt']].
    expand output@SenderB(i,j1); expand output@SenderB(i,j1').
    rewrite snd_pair in Eq0.
    rewrite snd_pair in Eq0'.
    rewrite fst_pair in Eq2.
    rewrite snd_pair in Eq2.
    rewrite snd_pair in Eq2.
    rewrite fst_pair in Eq2'.
    rewrite snd_pair in Eq2'.
    rewrite snd_pair in Eq2'.
    rewrite fst_pair in Eq1.
    rewrite fst_pair in Eq1.
    rewrite fst_pair in Eq1'.
    rewrite fst_pair in Eq1'.

    assert (j1 = j1' || j1 <> j1') as H => //.
    case H.
    (* case j1 = j1' *)
    left.
    split => //.

    (* case j1 <>j1' *)
    right.
    split.
    rewrite -Eq1 in *; rewrite -Eq1' in *; by auto.
    rewrite -Eq2 in *; rewrite -Eq2' in *.
    
    executable ReceiverA(i,j) => //; intro HexecPred.
    executable ReceiverA(i,j') => //; intro HexecPred'.

    assert(SenderB(i,j1) <SenderB(i,j1') || SenderB(i,j1') <SenderB(i,j1))=> //.
    case H0.

    (* SenderB(i,j1) <SenderB(i,j1') *)
    use counterIncreaseStrictSB with i, j1', SenderB(i,j1) => //.
    intro U. 
    apply orderStrict in U; by auto.
    split => //.
    use HexecPred' with SenderB(i,j1') =>//.

    (*  SenderB(i,j1') <SenderB(i,j1) *)
    (*  Rmq: Ce bout de preuve est semblable au 4 lignes precedentes mais le apply ne fait 
    pas l'affaire car les arguments ne sont pas instanties dans l'ordre qu'il me faut *) 
    use counterIncreaseStrictSB with i, j1, SenderB(i,j1') => //.
    intro U.
    use orderStrict with cellB(i)@SenderB(i,j1), cellB(i)@SenderB(i,j1') =>//.
    split => //.
    use HexecPred with SenderB(i,j1) =>//.
Qed.


(* 2nd property w.r.t A and B *)
goal injectivityAB(i,j,j':index) :
  happens(ReceiverA(i,j)) && happens(ReceiverB(i,j')) =>
    exec@ReceiverA(i,j) && exec@ReceiverB(i,j') => 
      (fst(fst(input@ReceiverA(i,j))) = fst(fst(input@ReceiverB(i,j')))
      && snd(snd(fst(input@ReceiverA(i,j)))) = snd(snd(fst(input@ReceiverB(i,j')))))
      ||
      (fst(fst(input@ReceiverA(i,j))) <> fst(fst(input@ReceiverB(i,j')))
      && snd(snd(fst(input@ReceiverA(i,j)))) <> snd(snd(fst(input@ReceiverB(i,j'))))).

Proof.
  intro [Hap Hap'] [Hexec Hexec'].
  use authA with i,j => //. destruct H as [j1 [Ord Eq0 Eq1 Eq2 HCpt]].
  use authB with i,j' => //.destruct H as [j1' [Ord' Eq0' Eq1' Eq2' HCpt']].
  expand output@SenderB(i,j1); expand output@SenderA(i,j1').
  rewrite snd_pair in Eq0.
  rewrite snd_pair in Eq0'.
  rewrite fst_pair in Eq2.
  rewrite snd_pair in Eq2.
  rewrite snd_pair in Eq2.
  rewrite fst_pair in Eq2'.
  rewrite snd_pair in Eq2'.
  rewrite snd_pair in Eq2'.
  rewrite fst_pair in Eq1.
  rewrite fst_pair in Eq1.
  rewrite fst_pair in Eq1'. 
  rewrite fst_pair in Eq1'.

  rewrite -Eq1 in *.
  rewrite -Eq1' in *.
  rewrite -Eq2 in *.
  rewrite -Eq2' in *.

  right.
  split => //.

  executable ReceiverA(i,j) => //; intro HexecPred.
  executable ReceiverB(i,j') => //; intro HexecPred'.

  assert(SenderB(i,j1) <ReceiverB(i,j') || ReceiverB(i,j') <SenderB(i,j1))=> //.
  case H.

 (* SenderB(i,j1) < ReceiverB(i,j') *)
 use counterIncreaseStrictRB with i, j',SenderB(i,j1) => //.
 expand cellB(i)@ReceiverB(i,j').
 use orderEqSucc with cellB(i)@SenderB(i,j1), cellB(i)@pred(ReceiverB(i,j')) => //.
 case H0.
 rewrite -H0 in HCpt'.
 intro U.
 use  orderStrict with cellB(i)@SenderB(i,j1), cellA(i)@SenderA(i,j1') => //.
 use  orderTrans with  cellB(i)@SenderB(i,j1), cellB(i)@pred(ReceiverB(i,j')), cellA(i)@SenderA(i,j1') => //.
 intro U.
 use  orderStrict with cellB(i)@SenderB(i,j1), cellA(i)@SenderA(i,j1') => //.


(* ReceiverB(i,j') <  SenderB(i,j1) *)
 assert(SenderA(i,j1') <ReceiverA(i,j) || ReceiverA(i,j) <SenderA(i,j1'))=> //.
 case H0.

   (* SenderA(i,j1') < ReceiverA(i,j) *)
   (* as in the previous case *)
   use counterIncreaseStrictRA with i, j,SenderA(i,j1') => //.
   expand cellA(i)@ReceiverA(i,j).
   use orderEqSucc with cellA(i)@SenderA(i,j1'), cellA(i)@pred(ReceiverA(i,j)) => //.
   case H1.
   rewrite -H1 in HCpt.
   intro U.
   use  orderStrict with cellB(i)@SenderB(i,j1), cellA(i)@SenderA(i,j1') => //.
   use  orderTrans with  cellA(i)@SenderA(i,j1'), cellA(i)@pred(ReceiverA(i,j)), cellB(i)@SenderB(i,j1) => //.
   intro U.
   use  orderStrict with cellB(i)@SenderB(i,j1), cellA(i)@SenderA(i,j1') => //.

   (* ReceiverA(i,j) < SenderA(i,j1') *)
   (* We have SendB < ReceiveA < SendA < ReceiveB < SendB ==> contradiction *)
   auto.
   Qed.


(* 2nd property w.r.t. B and B *)
(* Similar to the case w.r.t. A and A *)
