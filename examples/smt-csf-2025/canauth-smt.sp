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

mutex lA:1.
mutex lB:1.

process ReceiverA(i,j:index) =
  lock lA(i);
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellA(i) ~< snd(snd(fst(x)))
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(x))>,sk(i))
  then
    cellA(i) := mySucc(cellA(i));
    out(cS,ok);
    unlock lA(i)
  else
    unlock lA(i)

process ReceiverB(i,j:index) =
  lock lB(i);
  in(cR,x);
  if fst(snd(fst(x))) = SIGN
     && cellB(i) ~< snd(snd(fst(x)))
     && snd(x) = hmac(<snd(snd(fst(x))),fst(fst(x))>,sk(i))
  then
    cellB(i) := mySucc(cellB(i));
    out(cS,ok);
    unlock lB(i)
  else
    unlock lB(i)

process SenderA(i,j:index) =
  lock lA(i);
  cellA(i) := mySucc(cellA(i));
  out(cR,<<msgA(i,j),<SIGN,cellA(i)>>,hmac(<cellA(i),msgA(i,j)>,sk(i))>);
  unlock lA(i)

process SenderB(i,j:index) =
  lock lB(i);
  cellB(i) := mySucc(cellB(i));
  out(cR,<<msgB(i,j),<SIGN,cellB(i)>>,hmac(<cellB(i),msgB(i,j)>,sk(i))>);
  unlock lB(i)

system ((!_i !_j ReceiverA(i,j)) | (!_i !_j SenderA(i,j)) |
        (!_i !_j ReceiverB(i,j)) | (!_i !_j SenderB(i,j))).

(* LIBRARIES *)

include Real.

(* f_apply *)

lemma fst_apply (x,y : message) : x = y => fst(x) = fst(y).
Proof. auto. Qed.

lemma snd_apply (x,y : message) : x = y => snd(x) = snd(y).
Proof. auto. Qed.

(* AXIOMS *)

axiom [any] orderSucc (n,n':message): n = n' => n ~< mySucc(n').

axiom [any] orderTrans (n1,n2,n3:message): (n1 ~< n2 && n2 ~< n3) => n1 ~< n3.

axiom [any] orderStrict (n1,n2:message): n1 = n2 => n1 ~< n2 => false.

axiom [any] orderEqSucc (n1,n2:message):
  (n1 ~< mySucc(n2)) => ((n1 = n2) || n1 ~< n2).

hint smt orderSucc.
hint smt orderTrans.
hint smt orderStrict.
hint smt orderEqSucc.

(* The counter increases (not strictly) between t' and t when t' < t. *)

lemma counterIncreaseA (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellA(i)@t' ~< cellA(i)@t ||
    cellA(i)@t' = cellA(i)@t).
Proof.
  induction t. smt ~steps:26420.
Qed.

lemma counterIncreaseB (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellB(i)@t' ~< cellB(i)@t ||
    cellB(i)@t' = cellB(i)@t).
Proof.
  induction t. smt ~steps:89137.
Qed.


(* The counter cellA(i) strictly increases between t and t'
   when t < t' and (t' = SenderA(i,j1) or t' = ReceiverA(i,j1)). *)

lemma counterIncreaseStrictSA(i,j1:index, t:timestamp):
  happens(SenderA(i,j1)) =>
    (t < SenderA(i,j1) && exec@SenderA(i,j1)) =>
      cellA(i)@t ~< cellA(i)@SenderA(i,j1).
Proof.
  use counterIncreaseA. smt ~steps:18245.
Qed.

lemma counterIncreaseStrictRA (i,j1:index, t:timestamp):
  happens(ReceiverA(i,j1)) =>
    (t < ReceiverA(i,j1) && exec@ReceiverA(i,j1)) =>
      cellA(i)@t ~< cellA(i)@ReceiverA(i,j1).
Proof.
  use counterIncreaseA. smt ~steps:22516.
Qed.

(* The counter cellB(i) strictly increases between t and t'
   when t < t' and (t' = SenderB(i,j1) or t' = ReceiverB(i,j1)). *)

lemma counterIncreaseStrictSB (i,j1:index, t:timestamp):
  happens(SenderB(i,j1)) =>
    (t < SenderB(i,j1) && exec@SenderB(i,j1)) =>
      cellB(i)@t ~< cellB(i)@SenderB(i,j1).
Proof.
  use counterIncreaseB. smt ~steps:24389.
Qed.

lemma counterIncreaseStrictRB (i,j1:index, t:timestamp):
  happens(ReceiverB(i,j1)) =>
    (t < ReceiverB(i,j1) && exec@ReceiverB(i,j1)) =>
      cellB(i)@t ~< cellB(i)@ReceiverB(i,j1).
Proof.
  use counterIncreaseB. smt ~steps:30898.
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
  use counterIncreaseStrictRA.
  euf H3; smt ~steps:12695.
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
  use counterIncreaseStrictRB.
  euf H3; smt ~steps:16178.
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
  use counterIncreaseStrictSB.
  use authA.
  smt ~steps:66925.  
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
  use counterIncreaseStrictRB.
  use counterIncreaseStrictRA.
  use authA.
  use authB.
  smt ~prover:CVC5 ~steps:82495.
Qed.

(* 2nd property w.r.t. B and B *)
(* Similar to the case w.r.t. A and A *)
