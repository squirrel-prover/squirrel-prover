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
abstract order : message->message->message

(* PROCESSES *)

process Receiver(i,j:index) =
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && order(cellR(i),snd(snd(fst(x)))) = orderOk
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(fst(x)))>,sk(i))
  then 
    cellR(i) := mySucc(cellR(i));
    out(cS,ok)

process Sender(i,j:index) =
  cellS(i) := mySucc(cellS(i));
  out(cR,<<msg(i,j),<SIGN,cellS(i)>>,hmac(<cellS(i),msg(i,j)>,sk(i))>)

system ((!_i !_j Receiver(i,j)) | (!_i !_j Sender(i,j))).

(* AXIOMS *)

axiom orderSucc : forall (n:message), order(n,mySucc(n)) = orderOk
axiom orderTrans :
  forall (n1,n2,n3:message),
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
    => order(n1,n3) = orderOk
axiom orderStrict : 
  forall (n1,n2:message), n1 = n2 => order(n1,n2) <> orderOk.

(** HELPING LEMMAS *)

(* The counter increases strictly at each update. *)
goal counterIncreasePred(i,j:index): 
  happens(Sender(i,j)) =>
    order(cellS(i)@pred(Sender(i,j)),cellS(i)@Sender(i,j)) = orderOk.
Proof.
  intro Hap.  
  use orderSucc with cellS(i)@pred(Sender(i,j)).
  expand cellS.  
  assumption.
Qed.

(* À reprendre. *)
goal counterIncrease:
  forall (t':timestamp), forall (t:timestamp), forall (i,j:index),
    happens(t,t') =>
      exec@t' && t < Sender(i,j) && Sender(i,j) <= t' =>
        order(cellS(i)@t,cellS(i)@t') = orderOk.
Proof.
  induction.
  intro t' IH0 t i j Hap [Hexec Ht Ht'].
  assert (t = pred(t') || t < pred(t')) as H0 => //.
  case H0.

    (* case t = pred(t') *)
    rewrite !H0. 
    assert (pred(t') = Sender(i,j) || pred(t') < Sender(i,j)) as H => //.
    case H.
      use counterIncreasePred with i,j => //.  
      assert t' = Sender(i,j) => //.
      use counterIncreasePred with i,j => //.

    (* case t < pred(t') *)
    assert 
      (pred(t') > Sender(i,j) || pred(t') = Sender(i,j) || pred(t') < Sender(i,j)) 
      as H => //.
    case H.
      (* case pred(t') > Sender(i,j) *)
      use IH0 with pred(t'),t,i as H1 => //.
      use H1 with j => //.
      use orderTrans with cellS(i)@t,cellS(i)@pred(t'),cellS(i)@t' => //.
      admit.
      repeat split => //.
      executable t' => //.
      intro Ht0. 
      use Ht0 with pred(t') => //.
      (* case pred(t') = Sender(i,j) *)
      use IH0 with pred(t'),t,i as H1 => //.
      use H1 with j => //.
      use orderTrans with cellS(i)@t,cellS(i)@pred(t'),cellS(i)@t' => //.
      admit.
      repeat split => //.
      executable t' => //.
      intro Ht0. 
      use Ht0 with pred(t') => //.
      (* pred(t') < Sender(i,j) *)
      assert Sender(i,j) = t' => //.
      admit.
Qed.

(* GOALS *)

goal auth(i,j:index) :
  happens(Receiver(i,j)) => cond@Receiver(i,j) => 
    exists (j':index), 
      Sender(i,j') < Receiver(i,j) 
      && snd(output@Sender(i,j')) = snd(input@Receiver(i,j)).
Proof.
  intro Hap Hcond.
  expand cond.
  destruct Hcond as [H1 H2 H3].
  euf H3.
  intro H4 H5 _.
  exists j0.
  repeat split; auto.
Qed.

goal injectivity(i,j,j':index) :
  happens(Receiver(i,j),Receiver(i,j')) =>
    exec@Receiver(i,j) && exec@Receiver(i,j') => 
      (fst(fst(fst(input@Receiver(i,j)))) = fst(fst(fst(input@Receiver(i,j'))))
      && snd(snd(fst(input@Receiver(i,j)))) = snd(snd(fst(input@Receiver(i,j')))))
      ||
      (fst(fst(fst(input@Receiver(i,j)))) <> fst(fst(fst(input@Receiver(i,j'))))
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
        use counterIncrease with Sender(i,j1),Sender(i,j0),i,j1 => //.
        use orderStrict with cellS(i)@Sender(i,j0),cellS(i)@Sender(i,j1) => //.
        repeat split => //.
        use HexecPred' with Sender(i,j1) => //.
        use counterIncrease with Sender(i,j0),Sender(i,j1),i,j0 => //.
        use orderStrict with cellS(i)@Sender(i,j1),cellS(i)@Sender(i,j0) => //.
        repeat split => //.
        use HexecPred with Sender(i,j0) => //.
Qed.
