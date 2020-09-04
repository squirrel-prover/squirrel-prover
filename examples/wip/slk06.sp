(*******************************************************************************
SLK06

T. van Deursen and S. Radomirović, ‘Attacks on RFID Protocols’, 
Cryptology ePrint Archive, vol. 2008, no. 310, pp. 1–56, Aug. 2009.

The protocol assumes that the reader and tag share the secrets k, ID, and PIN.
While ID and PIN are unique to each tag, k is equal for all tags the reader is
allowed to authenticate. 
The tag further stores the timestamp TSlast of the last successful mutual 
authentication initialized to 0 at the factory.
*******************************************************************************)

hash h

abstract ok : message
abstract error : message

abstract TSinit : message
abstract TSok : message
abstract TScompare : message->message->message
abstract TSnext : message->message

name k : message

name key : index->message
name idinit : index->message
name pin : index->message

mutable kT : index->message (* <ID,TSlast> in the specification *) 
mutable kR : index->message (* <ID,TSlast> in the specification *)

channel cT
channel cR

axiom stateTagInit : forall (i:index), kT(i)@init = <idinit(i),TSinit>
axiom stateReaderInit : forall (ii:index), kR(ii)@init = idinit(ii)

axiom TSaxiom :
  forall (x:message), TScompare(x,TSnext(x)) = TSok

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, x1);
  if TScompare(snd(kT(i)),snd(x1)) = TSok then
    out(cT, h(fst(kT(i)),key(i)));
    in(cR, x3);
    if x3 = h(<fst(kT(i)),pin(i)>,key(i)) then
      kT(i) := < h(<kT(i),pin(i)>,key(i)), snd(x1) >;
      out(cT, ok)
    else 
      out(cT, error) 
  else
    out(cT, error)

(* jj = generic reader's session *)
process reader(jj:index) =
  out(cR, <h(TSnext(snd(kR(jj))),k),TSnext(snd(kR(jj)))>);
  in(cT, x2);
  try find ii such that x2 = h(kR(ii), key(ii)) in  
    (* in this conditional, kR(ii) should be the value BEFORE the update of this action,
    but we cannot write something like kR(ii)@pred(this) *)
    kR(ii) := h(<kR(ii),<pin(ii),TSnext(snd(kR(jj)))>>,key(ii));
    out(cR, h(<kR(ii),pin(ii)>,key(ii))) 
    (* idem *)
  else 
    out(cR, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).

goal auth_R :
  forall (jj,ii:index),
    cond@R1(jj,ii) =>
      ( exists (i,j:index), T(i,j) < R1(jj,ii) && output@T(i,j) = input@R1(jj,ii) ).
Proof.
intros.
expand cond@R1(jj,ii).
(* TODO *) admit.
Qed.
