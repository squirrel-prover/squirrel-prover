(*******************************************************************************
TOY EXAMPLE WITH STATE

Authentication goals with a toy protocol (bounded, generic reader).
*******************************************************************************)

hash hMsg
hash hState

abstract ok : message
abstract ko : message
abstract testOk : message

name seed : index->message
name keyState : index->message
name keyMsg : index->message

abstract readerTest : index->message->message

mutable kT : index->message

channel cT
channel cR

axiom stateTagInit : forall (i:index), kT(i)@init = seed(i)

axiom readerTestAxiom : 
  forall (i:index,x:message), 
  (readerTest(i,x)=testOk <=> 
    ( x=hMsg(hState(seed(i),keyState(i)),keyMsg(i))
      || x=hMsg(hState(hState(seed(i),keyState(i)),keyState(i)),keyMsg(i)))
      || x=hMsg(hState(hState(hState(seed(i),keyState(i)),keyState(i)),keyState(i)),keyMsg(i)) )
(* Not sure it is allowed to quantify over messages... *)

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  kT(i) := hState(kT(i),keyState(i));
  out(cT, hMsg(kT(i),keyMsg(i)))

(* k = generic reader's session *)
process reader(k:index) =
  in(cT,x);
  if exists (i:index), readerTest(i,x)=testOk then
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

goal wa_R :
forall (k:index),
  cond@R(k) =>
  (exists (i,j:index), T(i,j) < R(k) && output@T(i,j) = input@R(k)).
Proof.
intros.
expand cond@R(k).
apply readerTestAxiom to i,input@R(k).
apply H0.
case H2.
euf M1. exists i,j.
euf M1. exists i,j.
euf M1. exists i,j.
Qed.
