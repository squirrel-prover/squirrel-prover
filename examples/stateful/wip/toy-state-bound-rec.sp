(*******************************************************************************
TOY EXAMPLE WITH STATE

Authentication goals with a toy protocol (bounded, generic reader).

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

abstract deltaZero : message (* representing the integer 0 *)
abstract deltaMax : message (* representing the bound *)
abstract myPred : message->message

(* the try find construct does not allow to get a return value (the value with which
the database should be updated), so we use a private function updateReader *)
abstract updateReader : index->message->message (* should be private *)

abstract testOk : message
abstract readerTest : index->message->message->message->message

abstract stacked : index->message->message->message

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  kT(i) := hState(kT(i),keyState(i));
  out(cT, hMsg(kT(i),keyMsg(i)))

(* k = generic reader's session *)
process reader(k:index) =
  in(cT,x);
  try find ii such that readerTest(ii,kR(ii),x,deltaMax) = testOk in
    kR(ii) := updateReader(ii,x);
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

axiom deltaMaxAxiom : myPred(deltaZero) = deltaZero.

axiom updateReaderAxiom (i:index,xk:message):
    updateReader(i,hMsg(hState(xk,keyState(i)),keyMsg(i))) = hState(xk,keyState(i)).

axiom readerTestOk (i:index,xkR:message,x:message,delta:message):
  ( readerTest(i,xkR,x,delta) = testOk )
  <=> 
  ( x = hMsg(hState(xkR,keyState(i)),keyMsg(i))
    || readerTest(i,hState(xkR,keyState(i)),x,myPred(delta)) = testOk ).

axiom readerTestNotOk (i:index,xkR:message,x:message):
 readerTest(i,xkR,x,deltaZero) <> testOk.

axiom stacked_init (i:index,x:message): stacked(i,x,x)=testOk.

axiom stacked_step (i:index,x,y:message):
  stacked(i,x,y)=testOk => stacked(i,x,hState(y,keyState(i)))=testOk.

goal auth_R_step (delta:message,k,ii:index):
  (* The auth property to prove is generalized over "stacked" database entries,
     so in this lemma we have a (non-prenex) quantification over messages. *)
  happens(R(k,ii)) =>
  (
  (* Property for myPred(delta). *)
  (forall (x:message), stacked(ii,kR(ii)@R(k,ii),x) = testOk =>
   readerTest(ii,x,input@R(k,ii),myPred(delta)) = testOk =>
   exists (i,j:index), T(i,j) < R(k,ii) && input@R(k,ii) = output@T(i,j)) =>
  (* Property for delta. *)
  (forall (x:message), stacked(ii,kR(ii)@R(k,ii),x) = testOk =>
   readerTest(ii,x,input@R(k,ii),delta) = testOk =>
   exists (i,j:index), T(i,j) < R(k,ii) && input@R(k,ii) = output@T(i,j))
  ).
Proof.
intro *.
use readerTestOk with ii,x,input@R(k,ii),delta.
use H0. case H2.
(* euf Meq0 ?
   Problème avec la variable x. *)
admit.
admit.
Qed.

goal auth_R :
  forall (k,ii:index,delta:message), 
    happens(R(k,ii)) =>
    ( readerTest(ii,kR(ii)@R(k,ii),input@R(k,ii),delta) = testOk
      => (exists (i,j:index), T(i,j) < R(k,ii) && input@R(k,ii) = output@T(i,j)) ).
Proof.
intro *.

use readerTestOk with ii,kR(ii)@R(k,ii),input@R(k,ii),deltaMax.
use H0.
case H0.

  (* case H2 => direct case - sync *)
  assert kR(ii)@R(k,ii) = hState(kR(ii)@R(k,ii),keyState(ii)).
  admit.
  euf Meq1.
  (** Deux questions :
      1) Est-ce que la théorie autorise bien EUF ici, sachant qu'on a une variable
         de type message dans le séquent (même si pas dans M2) ?
      2) L'égalité M2, de la forme X = hState(X,K), n'est-elle pas un peu bizarre ? *)
  exists ii,j.

  (* case H2 => recursive case - desync *)
  use readerTestOk with ii,hState(kR(ii)@R(k,ii),keyState(ii)),input@R(k,ii),myPred(deltaMax).
  use H2.
  case H2.

    (* case H4 => direct case - sync *)

    (* case H4 => recursive case - desync *)

(* ETC *)
Qed.
