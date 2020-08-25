(*******************************************************************************
TOY EXAMPLE WITH STATE

Authentication goals with a toy protocol (bounded, generic reader).
*******************************************************************************)

hash hkey

abstract ok : message
abstract ko : message

name seed : index->message
name key : index->message

abstract testOk : message
abstract testKo : message
abstract readerTest : index->message->message->message->message
(* parser n'accepte pas boolean pour une déclaration abstract *)

abstract deltaMin : message
abstract deltaMax : message
abstract myPred : message->message

mutable kT : index->message 
mutable kR : index->message

channel cT
channel cR

axiom stateTagInit : forall (i:index), kT(i)@init = seed(i)
axiom stateReaderInit : forall (ii:index), kR(ii)@init = seed(ii) 

(* Not sure it is allowed to quantify over messages... *)
axiom readerTestAxiomOk : 
  forall (ii:index,xkR:message,delta:message,x:message),
  ( readerTest(ii,xkR,delta,x) = testOk ) <=> 
  ( x = hkey(xkR,key(ii)) (* sync *)
    || readerTest(ii,hkey(xkR,key(ii)),myPred(delta),x) = testOk ) (* desync: tag "ahead" the reader *)

axiom readerTestAxiomKo : 
  forall (ii:index,xkR:message,delta:message,x:message),
  ( readerTest(ii,xkR,delta,x) = testKo ) <=> ( readerTest(ii,xkR,delta,x) <> testOk )

(* ??? axioms related to deltaMin/deltaMax and myPred *)
(* utiliser plutôt le type index car celui-ci est interprété dans un domaine fini d'entiers ? *)

(*    
      x=hMsg(hState(<seed(i),n>,keyState(i)),keyMsg(i))
      || x=hMsg(hState(hState(seed(i),keyState(i)),keyState(i)),keyMsg(i)))
      || x=hMsg(hState(hState(hState(seed(i),keyState(i)),keyState(i)),keyState(i)),keyMsg(i)) )
*)

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  kT(i) := hkey(kT(i),key(i));
  out(cT, kT(i))

(* k = generic reader's session *)
process reader(k:index) =
  in(cT,x);
  try find ii such that readerTest(ii,kR(ii),deltaMax,x) = testOk in
    kR(ii) := x;
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

goal auth_R :
forall (t:timestamp), forall (k,ii:index),
  (t = R(k,ii) && cond@R(k,ii)) =>
  (exists (i,j:index), T(i,j) < R(k,ii) && output@T(i,j) = input@R(k,ii)).
Proof.
intros.
expand cond@R(k,ii).
(* bug : M0 devrait parler de kR(ii)@pred(R(k,ii) *)
apply readerTestAxiomOk to ii,kR(ii)@R(k,ii),deltaMax,input@R(k,ii).
apply H0.
case H2.

assert hkey(kR(ii)@R(k,ii),key(ii)) = kR(ii)@R(k,ii).
euf M2.
exists ii,j.



(* TODO *) admit.
Qed.
