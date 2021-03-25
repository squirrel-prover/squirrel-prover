(*******************************************************************************
SLK06

T. van Deursen and S. Radomirović, ‘Attacks on RFID Protocols’,
Cryptology ePrint Archive, vol. 2008, no. 310, pp. 1–56, Aug. 2009.

The protocol assumes that the reader and tag share the secrets k, ID, and PIN.
While ID and PIN are unique to each tag, k is equal for all tags the reader is
allowed to authenticate.
The tag further stores the timestamp TSlast of the last successful mutual
authentication initialized to 0 at the factory.

R -> T : <h(k,TS),TS>
T -> R : h(ID)               if TS > TSlast
         ID := h(ID,PIN,TS)
         TSlast := TS
R -> T : h(ID,PIN)
         ID' := h(ID,PIN,TS)
*******************************************************************************)

(*******************************************************************************
Trying to prove the secret of state values with phases.
*******************************************************************************)

set autoIntro=false.

abstract ok : message
abstract error : message

abstract TSinit : message
abstract TSorderOk : message
abstract TSorder : message->message->message
abstract TSnext : message->message

name k : message
name key1 : message
name key2 : message
name key3 : message

hash h
hash h1
hash h2
hash h3

name idinit : index->message
name pin : index->message

mutable kT(i:index) : message = <idinit(i),TSinit>
mutable kR(ii:index) : message = idinit(ii)
mutable TS : message = TSinit

channel cT
channel cR
channel c

name nIdeal : index->message

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, x1);
  if fst(x1) = h(snd(x1),k) && TSorder(snd(kT(i)),snd(x1)) = TSorderOk then
    out(cT, h1(fst(kT(i)),key1));
    in(cR, x3);
    if x3 = h2(<fst(kT(i)),pin(i)>,key2) then
      kT(i) := <h3(<<fst(kT(i)),pin(i)>,snd(x1)>,key3), snd(x1)>;
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
  try find ii such that x2 = h1(kR(ii), key1) in
    let m = h2(<kR(ii),pin(ii)>,key2) in
    kR(ii) := h3(<<kR(ii),pin(ii)>,TS>,key3);
    out(cR, m)
  else
    out(cR, error)

process outReaderState(i:index) =
  out(cR, diff(kR(i),nIdeal(i)))

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))
        | (!_i P: outReaderState(i))
        | !_kk (in(c,m); out(c,h1(m,key1)))
        | !_kk (in(c,m); out(c,h2(m,key2)))
        | !_kk (in(c,m); out(c,h3(m,key3)))).

axiom phases :
  forall (t:timestamp), happens(t) =>
  ( exists (i:index), t = P(i) ) || ( forall (i:index), happens(P(i)) => t < P(i) ).

equiv secretTagState.
Proof.
induction t.

admit.
admit.
admit.
admit.
admit.
admit.
admit.

expandall.
fa 0. fa 1. fa 1.
(* Here, kR(i)@pred(P(i,j)) is equal to h3(m,key3) with m already hased
in the frame, so I don't see how we can use PRF. *)

admit.
admit.
admit.
admit.
Qed.
