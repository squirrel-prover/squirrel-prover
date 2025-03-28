(*******************************************************************************
CANAUTH

Vincent Cheval, Véronique Cortier, and Mathieu Turuani.
“A Little More Conversation, a Little Less Action, a Lot More Satisfaction:
Global States in ProVerif”.
CSF 2018.

Sender -> Receiver : <ctrS,msg>, hmac(<ctrS,msg>,sk)
                     ctrS := ctrS+1 
Receiver -> Sender : input x, check x and whether ctr_received > ctrR
                     ctrR := ctr_received

An agent has a cell which is used to store a counter.
This counter is incremented on a send action, and set up to the reveived value on a receive action.

HELPING LEMMAS
- counter increase

SECURITY PROPERTIES
- authentication on one side 
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
  if  cellA(i) ~< fst(fst(x))
   && snd(x) = hmac(fst(x),sk(i))
  then
    cellA(i) := fst(fst(x));
    out(cS,ok)

process ReceiverB(i,j:index) =
  in(cR,x);
  if cellB(i) ~< fst(fst(x))
  && snd(x) = hmac(fst(x),sk(i))
  then
    cellB(i) := fst(fst(x));
    out(cS,ok)

process SenderA(i,j:index) =
  cellA(i) := mySucc(cellA(i));
  out(cR, <<cellA(i),msgA(i,j)>, hmac(<cellA(i),msgA(i,j)>,sk(i))>)

process SenderB(i,j:index) =
  cellB(i) := mySucc(cellB(i));
  out(cR,<<cellB(i),msgB(i,j)>, hmac(<cellB(i),msgB(i,j)>,sk(i))>)

system ((!_i !_j RA: ReceiverA(i,j)) | (!_i !_j SA: SenderA(i,j)) |
        (!_i !_j RB: ReceiverB(i,j)) | (!_i !_j SB: SenderB(i,j))).

(*******************************************************************************)

(* LIBRARIES *)

include Real.

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

lemma ctrIncA (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  ( cellA(i)@t' ~< cellA(i)@t ||
    cellA(i)@t' = cellA(i)@t).
Proof.
induction t. smt ~steps:21115.
Qed.

(* Authentication w.r.t. A *)

lemma authA (i,j:index) :
  happens(RA(i,j)) => exec@RA(i,j) =>
  (exists (j':index),
    SB(i,j') < RA(i,j)
    && fst(output@SB(i,j')) = fst(input@RA(i,j))).
Proof.
  intro Hap @/exec @/cond [H1 H2 H3].
  use ctrIncA.
  euf H3; smt ~steps:23546.
Qed.

lemma noReplay (i,i',j,j':index) : 
  happens(RA(i,j)) => exec@RA(i,j)
   => happens(RA(i',j')) => exec@RA(i',j') 
   => (i<>i' || j<>j')  
   => fst(input@RA(i,j)) <> fst(input@RA(i',j')).
Proof. 
 use authA. use ctrIncA. smt ~prover:Z3 ~steps:109224.
Qed.
