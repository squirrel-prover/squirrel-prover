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

PROOFS
- authentication
- injectivity
*******************************************************************************)

set autoIntro = false.

hash hmac

name sk : index -> message
name msg : index -> index -> message

abstract SIGN : message
abstract myZero : message
abstract ok : message

mutable cellR(i:index) : message = myZero
mutable cellS(i:index) : message = myZero

channel cR
channel cS

(* mySucc function for counter *)
abstract mySucc : message->message

(* order relation for counter *)
abstract orderOk : message
abstract (~<) : message->message->message

(* PROCESSES *)

process Receiver(i,j:index) =
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellR(i) ~< snd(snd(fst(x))) = orderOk
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(x))>,sk(i))
  then 
    cellR(i) := mySucc(cellR(i));
    out(cS,ok)

process Sender(i,j:index) =
  cellS(i) := mySucc(cellS(i));
  out(cR,<<msg(i,j),<SIGN,cellS(i)>>,hmac(<cellS(i),msg(i,j)>,sk(i))>)

system ((!_i !_j Receiver(i,j)) | (!_i !_j Sender(i,j))).

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

axiom orderSucc : forall (n:message), n ~< mySucc(n) = orderOk
axiom orderTrans :
  forall (n1,n2,n3:message),
    (n1 ~< n2 = orderOk && n2 ~< n3 = orderOk)
    => n1 ~< n3 = orderOk
axiom orderStrict : 
  forall (n1,n2:message), n1 = n2 => n1 ~< n2 <> orderOk.

(** HELPING LEMMAS *)

(* The counter cellS(i) strictly increases at each action Sender(i,j). *)
goal counterIncreaseUpdate(i,j:index): 
  happens(Sender(i,j)) => cond@Sender(i,j) =>
    cellS(i)@pred(Sender(i,j)) ~< cellS(i)@Sender(i,j) = orderOk.
Proof.
  intro Hap Hcond.  
  use orderSucc with cellS(i)@pred(Sender(i,j)).
  expand cellS.  
  assumption.
Qed.

(* The counter cellS(i) increases (not strictly) between pred(t) and t. *)
goal counterIncreasePred(t:timestamp, i:index): 
  happens(t) => (t > init && exec@t) =>
    ( cellS(i)@pred(t) ~< cellS(i)@t = orderOk
      || cellS(i)@pred(t) = cellS(i)@t ).
Proof.
  intro Hap [Ht Hexec].  
  case t => //.

  intro [i0 j _].
  case (i = i0) => _.
    (* i = i0 *)
    left.
    use orderSucc with cellS(i)@pred(t).
    expand cellS.  
    assumption.
    (* i <> i0 *)
    right.
    by rewrite /cellS if_false.
Qed.

(* The counter cellS(i) increases (not strictly) between t' and t when t' < t. *)
goal counterIncrease:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
    exec@t && t' < t =>
    ( cellS(i)@t' ~< cellS(i)@t = orderOk || 
      cellS(i)@t' = cellS(i)@t).
Proof.
  induction.
  intro t IH0 t' i Hap [Hexec Ht'].
  assert (t' = pred(t) || t' < pred(t)) as H0; 
  1: case t; constraints. 
  case H0.

  (* case t' = pred(t) *)
  rewrite !H0. 
  by apply counterIncreasePred.

  (* case t' < pred(t) *)
  use IH0 with pred(t),t',i as H1 => //.
  use counterIncreasePred with t,i as H3 => //.
  case H1 => //.
    (* case H1 - 1/2 *)
    case H3 => //.
      by left; apply orderTrans _ (cellS(i)@pred(t)) _.
      (* case H1 - 2/2 *)
      by case H3; [1: left | 2 : right].
  
      simpl.
      executable t => // H1. 
      by apply H1.
Qed.

(* The counter cellS(i) increases strictly between Sender(i,j0) and Sender(i,j1)
   when Sender(i,j0) < Sender(i,j1). *)
goal counterIncreaseStrict(i,j0,j1:index): 
  happens(Sender(i,j1)) => 
    (Sender(i,j0) < Sender(i,j1) && exec@Sender(i,j1)) =>
      cellS(i)@Sender(i,j0) ~< cellS(i)@Sender(i,j1) = orderOk.
Proof.
  intro Hap [Ht Hexec].  
  use counterIncreaseUpdate with i,j1 => //.
  assert (
    Sender(i,j0) < pred(Sender(i,j1))
    || Sender(i,j0) = pred(Sender(i,j1))) as H => //.
  case H => //.
    use counterIncrease with pred(Sender(i,j1)),Sender(i,j0),i as H0 => //.
    case H0 => //.
      use orderTrans with
        cellS(i)@Sender(i,j0),
        cellS(i)@pred(Sender(i,j1)),
        cellS(i)@Sender(i,j1) => //.
Qed.

(* GOALS *)

goal auth(i,j:index) :
  happens(Receiver(i,j)) => cond@Receiver(i,j) => 
    exists (j':index), 
      Sender(i,j') < Receiver(i,j) 
      && snd(output@Sender(i,j')) = snd(input@Receiver(i,j))
      && fst(fst(output@Sender(i,j'))) = fst(fst(input@Receiver(i,j)))
      && snd(snd(fst(output@Sender(i,j')))) = snd(snd(fst(input@Receiver(i,j)))).
Proof.
  intro Hap Hcond.
  expand cond.
  destruct Hcond as [H1 H2 H3].
  euf H3.
  intro H4 H5 _.
  exists j0.
  repeat split => //.
Qed.

goal injectivity(i,j,j':index) :
  happens(Receiver(i,j),Receiver(i,j')) =>
    exec@Receiver(i,j) && exec@Receiver(i,j') => 
      (fst(fst(input@Receiver(i,j))) = fst(fst(input@Receiver(i,j')))
      && snd(snd(fst(input@Receiver(i,j)))) = snd(snd(fst(input@Receiver(i,j')))))
      ||
      (fst(fst(input@Receiver(i,j))) <> fst(fst(input@Receiver(i,j')))
      && snd(snd(fst(input@Receiver(i,j)))) <> snd(snd(fst(input@Receiver(i,j'))))).
Proof.
  intro Hap [Hexec Hexec'].
  executable Receiver(i,j) => //. intro HexecPred.
  executable Receiver(i,j') => //. intro HexecPred'.
  expand exec. expand cond.
  destruct Hexec as [Hexec [H1 H2 H3]].
  destruct Hexec' as [Hexec' [H1' H2' H3']].
  assert (j=j' || j<>j') as H => //.
  case H.
    (* case j = j' *)
    left. auto.
    (* case j <> j' *)
    euf H3. euf H3'. intro *.
    assert (j0=j1 || j0<>j1) as H0 => //.
    case H0.
      (* case j0 = j1 *)
      left. auto.
      (* case j0 <> j1 *)
      right. split. intro *.
      assert msg(i,j1) = msg(i,j0) => //.
      intro *.
      assert cellS(i)@Sender(i,j1) = cellS(i)@Sender(i,j0) => //.
      assert 
        (Sender(i,j0) < Sender(i,j1) || Sender(i,j1) < Sender(i,j0)) 
        as H4 => //.
      case H4.
        use counterIncreaseStrict with i,j0,j1 => //.
        use orderStrict with cellS(i)@Sender(i,j0),cellS(i)@Sender(i,j1) => //.
        repeat split => //.
        use HexecPred' with Sender(i,j1) => //.
        use counterIncreaseStrict with i,j1,j0 => //.
        use orderStrict with cellS(i)@Sender(i,j1),cellS(i)@Sender(i,j0) => //.
        repeat split => //.
        use HexecPred with Sender(i,j0) => //.
Qed.

(******************************************************************************
(* This lemma is actually unused. *)
goal lastUpdateSender(t:timestamp,i:index):
  happens(t) =>
    ( cellS(i)@t = cellS(i)@init &&
      forall (j0:index), happens(Sender(i,j0)) => t < Sender(i,j0) )
    ||
    ( exists (j0:index),
        cellS(i)@t = cellS(i)@Sender(i,j0) && Sender(i,j0) <= t &&
        forall (j0':index), 
          happens(Sender(i,j0')) => Sender(i,j0') <= Sender(i,j0) || t < Sender(i,j0') ).
Proof.
  generalize t i.
  induction => t IH0 i Hap.
  case t;
  try (
    intro Eq; repeat destruct Eq as [_ Eq];
    use IH0 with pred(t),i as H1 => //;
    clear IH0;
    expand cellS;
    destruct H1 as [[_ H3] | [mi [_ _ H1]]];
    [ 1: left => /= mi *;
         by use H3 with mi |
      2: right;
         exists mi => /= j0' Hap';
         use H1 with j0' as H2 => //;
         by case H2; [ 1: left | 2 : right]]).

  (* init *)
  by intro *; left.

  (* interesting case *)
  intro [i0 j0 _].
  use IH0 with pred(t),i as H1; 2,3: auto.
  case H1.

    (**)
    destruct H1 as [H2 H3].
    case (i=i0) => H4.
    (* i = i0 *)
    right.
    exists j0 => /= j0' _. 
    by use H3 with j0'.

    (* i <> i0 *)
    left. 
    expand cellS.
    rewrite if_false => //=.
    intro j0' _.
    by use H3 with j0'.

    (**)
    simpl_left.
    case (i=i0) => H2.
    case (j0=j1) => H3.

    (* i = i0 && j0 = j1 *)
    constraints.
    (* i = i0 && j0 <> j1 *)
    right.
    exists j0. 
    simpl.
    auto.

    (* i <> i0 *)
    right.
    exists j1. 
    simpl.
    split; 1: by rewrite /cellS if_false.
    intro j0' _.
    use H0 with j0' as Ht; 2: assumption.
    by case Ht.
Qed.
*)
