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
hash h1
hash h2
hash h3

abstract ok : message
abstract error : message

abstract TSinit : message
abstract TSorderOk : message
abstract TSorder : message->message->message
abstract TSnext : message->message

name k : message

name key1 : index->message
name key2 : index->message
name key3 : index->message
name idinit : index->message
name pin : index->message

mutable kT : index->message (* <<ID_old,TSlast_old>,<ID,TSlast>> *) 
mutable kR : index->message (* <ID_old,ID> *) 
mutable TS : message

channel cT
channel cR

axiom stateTagInit : forall (i:index), kT(i)@init = <<idinit(i),TSinit>,<idinit(i),TSinit>>
axiom stateReaderInit : forall (ii:index), kR(ii)@init = <idinit(ii),idinit(ii)>
axiom stateTSInit : TS@init = TSinit

axiom TSaxiom :
  forall (x:message), TSorder(x,TSnext(x)) = TSorderOk

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, x1);
  if fst(x1) = h(snd(x1),k) && TSorder(snd(snd(kT(i))),snd(x1)) = TSorderOk then
    out(cT, h1(fst(snd(kT(i))),key1(i)));
    in(cR, x3);
    if x3 = h2(<fst(fst(kT(i))),pin(i)>,key2(i)) then
      kT(i) := <snd(kT(i)), <h3(<<fst(snd(kT(i))),pin(i)>,snd(x1)>,key3(i)), snd(x1)>>;
      out(cT, ok)
    else 
      out(cT, error) 
  else
    out(cT, error)

(* jj = generic reader's session *)
process reader(jj:index) =
  TS := TSnext(TS);
  out(cR, <h(TS,k),TS>);
  in(cT, x2);
  try find ii such that x2 = h1(fst(kR(ii)), key1(ii)) in  
    kR(ii) := <snd(kR(ii)),h3(<<snd(kR(ii)),pin(ii)>,TS>,key3(ii))>;
    out(cR, h2(<fst(kR(ii)),pin(ii)>,key2(ii)))
  else 
    out(cR, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).

goal auth_R1 :
forall (jj,ii:index),
  cond@R1(jj,ii) 
  =>
  (exists (j:index), T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii)).
Proof.
intros.
expand cond@R1(jj,ii).
assert input@R1(jj,ii) = h1(snd(kR(ii)@pred(R1(jj,ii))),key1(ii)).
euf M1.
exists j.
Qed.

goal auth_T1 :
forall (i,j:index),
  cond@T1(i,j)
  =>
  (exists (jj:index), R1(jj,i) < T1(i,j) && output@R1(jj,i) = input@T1(i,j)).
Proof.
intros.
expand cond@T1(i,j).
assert input@T1(i,j) = h2(<fst(snd(kT(i)@pred(T1(i,j)))),pin(i)>,key2(i)).
euf M1.
exists jj.
Qed.
