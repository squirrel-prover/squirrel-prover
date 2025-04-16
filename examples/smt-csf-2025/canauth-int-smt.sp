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

include Int.
open Int. 
include Core.

hash hmac

name sk : index -> message
name msgA : index * index -> message
name msgB : index * index -> message

abstract int_to_msg : int -> message
abstract msg_to_int : message -> int

abstract SIGN : message
abstract ok : message

mutable cellA(i:index) : int = 0
mutable cellB(i:index) : int = 0

channel cR
channel cS

(*op ( + ) : int -> int -> int.*)

(* PROCESSES *)

process ReceiverA(i,j:index) =
  in(cR,x);
  if  cellA(i) < msg_to_int(fst(fst(x)))
   && snd(x) = hmac(fst(x),sk(i))
  then
    cellA(i) := msg_to_int(fst(fst(x)));
    out(cS,ok)

process ReceiverB(i,j:index) =
  in(cR,x);
  if cellB(i) < msg_to_int(fst(fst(x)))
  && snd(x) = hmac(fst(x),sk(i))
  then
    cellB(i) := msg_to_int(fst(fst(x)));
    out(cS,ok)

process SenderA(i,j:index) =
  cellA(i) := (cellA(i) + 1);
  out(cR, <<int_to_msg(cellA(i)),msgA(i,j)>, hmac(<int_to_msg(cellA(i)),msgA(i,j)>,sk(i))>)

process SenderB(i,j:index) =
  cellB(i) := cellB(i)+1;
  out(cR,<<int_to_msg(cellB(i)),msgB(i,j)>, hmac(<int_to_msg(cellB(i)),msgB(i,j)>,sk(i))>)

system ((!_i !_j RA: ReceiverA(i,j)) | (!_i !_j SA: SenderA(i,j)) |
        (!_i !_j RB: ReceiverB(i,j)) | (!_i !_j SB: SenderB(i,j))).

(*******************************************************************************)

(* LIBRARIES *)


(* AXIOMS *)

axiom [any] int_msg (n:int) : msg_to_int(int_to_msg(n)) = n.

hint smt int_msg. 

(* The counter increases (not strictly) between t' and t when t' < t. *)

lemma ctrIncA (t, t':timestamp, i:index):
  happens(t) =>
  exec@t =>
  t' < t =>
  cellA(i)@t' <= cellA(i)@t.
Proof.
induction t. smt ~steps:21130.
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
  euf H3; smt ~prover:CVC5 ~steps:21144.
Qed.

lemma noReplay (i,i',j,j':index) : 
  happens(RA(i,j)) => exec@RA(i,j)
   => happens(RA(i',j')) => exec@RA(i',j') 
   => (i<>i' || j<>j')  
   => fst(input@RA(i,j)) <> fst(input@RA(i',j')).
Proof. 
 use authA. use ctrIncA. smt ~prover:Z3 ~steps:845578.
Qed.
