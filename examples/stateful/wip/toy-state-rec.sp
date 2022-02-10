(*******************************************************************************
TOY EXAMPLE WITH STATE

Authentication goals with a toy protocol.

In this model, the database lookup performed by the reader is modelled with 
a recursive axiom.

/!\ quantifications over variables of type message
*******************************************************************************)

hash hState
hash hMsg

abstract ok : message
abstract ko : message

name seed : index->message
name keyState : index->message
name keyMsg : index->message

mutable kT(i:index) : message = seed(i)
mutable kR(ii:index) : message = seed(ii)

channel cT
channel cR

abstract deltaInit : message
abstract myPred : message->message

(* the try find construct does not allow to get a return value (the value with which
the database should be updated), so we use a private function updateReader *)
abstract updateReader : index->message->message (* should be private *)

abstract testOk : message
abstract readerTest : index->message->message->message->message

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  kT(i) := hState(kT(i),keyState(i));
  out(cT, hMsg(kT(i),keyMsg(i)))

(* k = generic reader's session *)
process reader(k:index) =
  in(cT,x);
  try find ii such that readerTest(ii,kR(ii),x,deltaInit) = testOk in
    kR(ii) := updateReader(ii,x);
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

axiom updateReaderAxiom : 
  forall (i:index,xk:message), 
    updateReader(i,hMsg(hState(xk,keyState(i)),keyMsg(i))) = hState(xk,keyState(i)).

axiom readerTestOk :
  forall (i:index,xkR:message,x:message,delta:message),
  ( readerTest(i,xkR,x,delta) = testOk )
  <=> 
  ( x = hMsg(xkR,keyMsg(i))
    || readerTest(i,hState(xkR,keyState(i)),x,myPred(delta)) = testOk ).

goal auth_R :
  forall (k,ii:index), 
    happens(R(k,ii)) =>
    (cond@R(k,ii) => ( exists (i,j:index), T(i,j) < R(k,ii) && input@R(k,ii) = output@T(i,j) )).
Proof.
intro *.
expand cond@R(k,ii).
use readerTestOk with ii,kR(ii)@pred(R(k,ii)),input@R(k,ii),deltaInit.
use H0.
case H2.

  (* case H2 => direct case - sync *)
  euf Meq.
  exists ii,j.

  (* case H2 => recursive case - desync *)
  use readerTestOk with ii,hState(kR(ii)@pred(R(k,ii)),keyState(ii)),input@R(k,ii),myPred(deltaInit).
  use H2.
  case H4.

    (* case H4 => direct case - sync *)
    euf Meq0.
    exists ii,j.

    (* case H4 => recursive case - desync *)

(* ETC *)
admit.
Qed.
