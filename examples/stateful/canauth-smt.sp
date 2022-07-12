(*******************************************************************************
CANAUTH using the smt tactic

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

set timeout=8.

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
abstract mySucc : message -> message

(* order relation for counter *)
abstract (~<) : message -> message -> boolean

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

goal fst_apply (x,y : message) : x = y => fst(x) = fst(y).
Proof. auto. Qed.


goal snd_apply (x,y : message) : x = y => snd(x) = snd(y).
Proof. auto. Qed.

(* AXIOMS *)

axiom orderSucc (n,n':message): n = n' => n ~< mySucc(n').

axiom orderTrans (n1,n2,n3:message): (n1 ~< n2 && n2 ~< n3) => n1 ~< n3.

axiom orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 => false.

axiom orderEqSucc (n1,n2:message):
  (n1 ~< mySucc(n2)) => ((n1 = n2) || n1 ~< n2).


hint smt orderSucc.
hint smt orderTrans.
hint smt orderStrict.
hint smt orderEqSucc.

(* The counter increases (not strictly) between t' and t when t' < t. *)

goal counterIncreaseA (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellA(i)@t' ~< cellA(i)@t ||
    cellA(i)@t' = cellA(i)@t).
Proof.
  induction t => t IH0 Hap Hexec Ht'. 
  case t => // [i_ j_ _]; revert IH0 Hexec; smt.
Qed.


goal counterIncreaseB (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellB(i)@t' ~< cellB(i)@t ||
    cellB(i)@t' = cellB(i)@t).
Proof.
  induction t => t IH0 Hap Hexec Ht'.
  case t => // [i_ j_ _];  revert IH0 Hexec; smt.
Qed.

goal counterIncreaseStrictRA (i,j1:index, t:timestamp):
  happens(ReceiverA(i,j1)) =>
    (t < ReceiverA(i,j1) && exec@ReceiverA(i,j1)) =>
      cellA(i)@t ~< cellA(i)@ReceiverA(i,j1).
Proof.
  intro H. expand cellA(i)@ReceiverA(i,j1).
  use counterIncreaseA as CIA. revert CIA.  smt.
Qed.

(* The counter cellB(i) strictly increases between t and t'
   when t < t' and (t' = SenderB(i,j1) or t' = ReceiverB(i,j1)). *)

goal counterIncreaseStrictSB (i,j1:index, t:timestamp):
  happens(SenderB(i,j1)) =>
    (t < SenderB(i,j1) && exec@SenderB(i,j1)) =>
      cellB(i)@t ~< cellB(i)@SenderB(i,j1).
Proof.
  intro H. expand cellB(i)@SenderB(i,j1).
  use counterIncreaseB as CIB. revert CIB. smt.
Qed.

goal counterIncreaseStrictRB (i,j1:index, t:timestamp):
  happens(ReceiverB(i,j1)) =>
    (t < ReceiverB(i,j1) && exec@ReceiverB(i,j1)) =>
      cellB(i)@t ~< cellB(i)@ReceiverB(i,j1).
Proof.
  intro H. expand cellB(i)@ReceiverB(i,j1).
  use counterIncreaseB as CIB. revert CIB. smt.
Qed.


(* SECURITY PROPERTIES *)

(* 1st property w.r.t. A *)
(* This security property is actually stronger than the one stated in
   the GSVerif paper. The send action has been done by agent B, and we
   also proved a lemma regarding counters.
   Moreover, we use this 1st property (authentication) to prove the
   2nd property (injectivity). *)

goal authA (i,j:index) :
  happens(ReceiverA(i,j)) => exec@ReceiverA(i,j) =>
  (exists (j':index),
    SenderB(i,j') < ReceiverA(i,j)
    && snd(output@SenderB(i,j')) = snd(input@ReceiverA(i,j))
    && fst(fst(output@SenderB(i,j'))) = fst(fst(input@ReceiverA(i,j)))
    && snd(snd(fst(output@SenderB(i,j')))) = snd(snd(fst(input@ReceiverA(i,j))))
    && cellA(i)@pred(ReceiverA(i,j)) ~< cellB(i)@SenderB(i,j')).
Proof.
  intro Hap @/exec @/cond [Hexecpred [H1 H2 H3]].
  revert H2 Hexecpred. 
  euf H3.
    + use counterIncreaseStrictRA as Hyp. revert Hyp. smt.
    + smt.
Qed.

(* 1st property w.r.t. B *)
goal authB(i,j:index) :
  happens(ReceiverB(i,j)) => exec@ReceiverB(i,j) =>
  (exists (j':index),
     SenderA(i,j') < ReceiverB(i,j)
     && snd(output@SenderA(i,j')) = snd(input@ReceiverB(i,j))
     && fst(fst(output@SenderA(i,j'))) = fst(fst(input@ReceiverB(i,j)))
     && snd(snd(fst(output@SenderA(i,j')))) = snd(snd(fst(input@ReceiverB(i,j))))
     && cellB(i)@pred(ReceiverB(i,j)) ~< cellA(i)@SenderA(i,j')).
Proof.
  intro Hap @/exec @/cond [Hexecpred [H1 H2 H3]].
  revert H2 Hexecpred.
  euf H3.
   + smt.
   + use counterIncreaseStrictRB as Hyp. revert Hyp. smt.
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

  use authA with i,j as H => //.
  destruct H as [j1 [Ord Eq0  Eq1 Eq2 HCpt]].
  use authA with i,j' as H => //.
  destruct H as [j1' [Ord' Eq0' Eq1' Eq2' HCpt']].

  case (j1 = j1') => H.
    + (* case j1 = j1' *)
      smt. 

    + (* case j1 <>j1' *)
      right.    
      split. 
        - smt. 
        - rewrite -Eq2 -Eq2' in *. expandall. simpl.
          assert (SenderB(i,j1) < SenderB(i,j1') ||
                  SenderB(i,j1') < SenderB(i,j1)) as H0 => //. case H0.

          * (* SenderB(i,j1) < SenderB(i,j1') *)
            use counterIncreaseStrictSB with i, j1', SenderB(i,j1) => //=. 
               ** revert H1. smt.
               ** executable ReceiverA(i,j') => // HexecPred.
                 by apply HexecPred.
          * (* SenderB(i,j1') < SenderB(i,j1) *)
            use counterIncreaseStrictSB with i, j1, SenderB(i,j1') => //=. 
               ** revert H1. smt.
               ** executable ReceiverA(i,j) => // HexecPred.
                 by apply HexecPred.
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
      use counterIncreaseStrictRB with i, j',SenderB(i,j1) as Meq => //. revert Meq HCpt'. smt.

    + (* ReceiverB(i,j') <  SenderB(i,j1) *)
      assert (SenderA(i,j1') <ReceiverA(i,j) ||
          ReceiverA(i,j) <SenderA(i,j1')) as H0 by auto.
      case H0 => //.
      (* SenderA(i,j1') < ReceiverA(i,j) *)
      use counterIncreaseStrictRA with i, j,SenderA(i,j1') as Meq => //. revert Meq HCpt. smt.
Qed.


(* 2nd property w.r.t. B and B *)
(* Similar to the case w.r.t. A and A *)
