(*******************************************************************************
TOY EXAMPLE WITH STATE

Authentication goals with a toy protocol.

In this model, the goal is to use multiset (as in Tamarin) to represent stack of
successive hashes.

/!\ quantifications over variables of type message
*******************************************************************************)

hash hState
hash hMsg

abstract ok : message
abstract ko : message

name seed : index->message
name keyState : index->message
name keyMsg : index->message

channel cT
channel cR

abstract delta : message (* the constant used in the multiset *)
abstract plus : message->message->message

abstract rangeOk : message
abstract range : message->message->message

abstract updateTag : index->message->message (* should be private *)
abstract updateReader : index->message->message (* should be private *)

mutable kT(i:index) : message = hState(<seed(i),delta>,keyState(i))
mutable kR(ii:index) : message = hState(<seed(ii),delta>,keyState(ii))

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  kT(i) := updateTag(i,kT(i));
  out(cT, hMsg(kT(i),keyMsg(i)))

(* k = generic reader's session *)
process reader(k:index) =
  in(cT,x);
  try find ii such that
    (exists (xkT:message), x = hMsg(xkT,keyMsg(ii)) && range(xkT,kR(ii)) = rangeOk)
  in
    kR(ii) := updateReader(ii,x);
    out(cR,ok)
  else
    out(cR,ko)

system ((!_k R: reader(k)) | (!_i !_j T: tag(i,j))).

(* range(kT,kR) = rangeOk iif there exists n, kT=h^n(kR) *)
axiom rangeAxiom :
  forall (xkT,xkR:message),
    range(xkT,xkR) = rangeOk
    <=> ( exists (i:index,z:message,z':message),
            xkT = hState(<seed(i),plus(z,z')>,keyState(i))
            && xkR = hState(<seed(i),z>,keyState(i)) ).
axiom updateTagAxiom :
  forall (i:index,z:message),
    updateTag(i,hState(<seed(i),z>,keyState(i))) = hState(<seed(i),plus(z,delta)>,keyState(i)).
axiom updateReaderAxiom :
  forall (ii:index,x:message), updateReader(ii,hMsg(x,keyMsg(ii))) = x.

goal auth_R :
  forall (k,ii:index,delta:message),
    happens(R(k,ii)) =>
    (cond@R(k,ii)
      => (exists (i,j:index), T(i,j) < R(k,ii) && input@R(k,ii) = output@T(i,j))).
Proof.
intro *.
expand cond@R(k,ii).

use rangeAxiom with xkT,kR(ii)@R(k,ii).
use H0.

use updateReaderAxiom with ii,xkT.
assert kR(ii)@R(k,ii) = xkT.
use H.
euf Meq4.
(* Error "Tactic failed: Key does not satisfy the syntactic side condition."
Coming from variable messages?  *)
Qed.
