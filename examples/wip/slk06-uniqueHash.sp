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

abstract ok : message
abstract error : message

abstract TSinit : message
abstract TSorderOk : message
abstract TSorder : message->message->message
abstract TSnext : message->message

name k : message
name key : message

hash h
hash hkey with oracle forall (m:message,sk:message), sk = key

name idinit : index->message
name pin : index->message

mutable kT : index->message (* <ID,TSlast> *)
mutable kR : index->message (* <ID> *)
mutable TS : message

channel cT
channel cR

axiom stateTagInit : forall (i:index), kT(i)@init = <idinit(i),TSinit>
axiom stateReaderInit : forall (ii:index), kR(ii)@init = idinit(ii)
axiom stateTSInit : TS@init = TSinit

axiom TSaxiom :
  forall (x:message), TSorder(x,TSnext(x)) = TSorderOk

axiom hashNotPair : 
  forall (m,x,y:message), hkey(m,key) <> <x,y>

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, x1);
  if fst(x1) = h(snd(x1),k) && TSorder(snd(kT(i)),snd(x1)) = TSorderOk then
    out(cT, hkey(fst(kT(i)),key));
    in(cR, x3);
    if x3 = hkey(<fst(kT(i)),pin(i)>,key) then
      kT(i) := <hkey(<<fst(kT(i)),pin(i)>,snd(x1)>,key), snd(x1)>;
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
  try find ii such that x2 = hkey(kR(ii), key) in
    let m = hkey(<kR(ii),pin(ii)>,key) in
    kR(ii) := hkey(<<kR(ii),pin(ii)>,TS>,key);
    out(cR, m)
  else
    out(cR, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).

goal lastUpdateTag_ :
forall (t:timestamp), forall (i:index),
  (kT(i)@t = kT(i)@init && forall (j':index) t < T1(i,j')) ||
  (exists j:index,
    kT(i)@t = kT(i)@T1(i,j) &&
    T1(i,j) <= t &&
    (forall (j':index), T1(i,j')<=T1(i,j) || t<T1(i,j'))).
Proof.
induction.
case t.
case H0.

substitute t,R(jj).
apply IH0 to pred(R(jj)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j. apply H1 to j'.
case H2.

substitute t,R1(jj,ii).
apply IH0 to pred(R1(jj,ii)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j. apply H1 to j'.
case H2.

substitute t,R2(jj).
apply IH0 to pred(R2(jj)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j. apply H1 to j'.
case H2.

substitute t,T(i1,j).
apply IH0 to pred(T(i1,j)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j1. apply H1 to j'.
case H2.

substitute t,T1(i1,j).
apply IH0 to pred(T1(i1,j)).
apply H0 to i.
case H1.
(* *)
assert (i=i1 || i<>i1).
case H2.
(* case i=i1 *)
right.
exists j.
(* case i<>i1 *)
left.
split.
case (if i = i1 then
       <hkey(<<fst(kT(i1)@pred(T1(i1,j))),pin(i1)>,snd(input@T(i1,j))>,key),
        snd(input@T(i1,j))>
       else kT(i)@pred(T1(i1,j))).
apply H1 to j'.
(* *)
assert (i=i1 || i<>i1).
case H2.
(* case i=i1 *)
right.
exists j.
(* case i<>i1 *)
right.
exists j1.
split.
case (if i = i1 then
       <hkey(<<fst(kT(i1)@pred(T1(i1,j))),pin(i1)>,snd(input@T(i1,j))>,key),
        snd(input@T(i1,j))>
       else kT(i)@pred(T1(i1,j))).
assert (j=j1 || j<>j1).
case H2.
apply H1 to j'.
case H2.
apply H1 to j'.
case H2.

substitute t,T2(i1,j).
apply IH0 to pred(T2(i1,j)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j1. apply H1 to j'.
case H2.

substitute t,T3(i1,j).
apply IH0 to pred(T3(i1,j)).
apply H0 to i.
case H1.
left. apply H1 to j'.
right. exists j1. apply H1 to j'.
case H2.

substitute t,init.
left.
Qed.

goal lastUpdateT :
forall (i,j:index),
  kT(i)@T(i,j) = kT(i)@init
  || (exists (j':index), kT(i)@T(i,j) =
       < hkey(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key),
         snd(input@T(i,j')) >).
Proof.
intros.
apply lastUpdateTag_ to T(i,j).
apply H0 to i.
case H1.
left.
right.
exists j1.
Qed.

goal lastUpdatePredT1 :
forall (i,j:index),
  kT(i)@pred(T1(i,j)) = kT(i)@init
  || (exists (j':index), kT(i)@pred(T1(i,j)) =
       < hkey(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key),
         snd(input@T(i,j')) >).
Proof.
intros.
apply lastUpdateTag_ to pred(T1(i,j)).
apply H0 to i.
case H1.
left.
right.
exists j1.
Qed.

goal lastUpdatePredR1 :
forall (jj,ii:index),
  kR(ii)@pred(R1(jj,ii)) = kR(ii)@init
  || (exists (jj':index),
       kR(ii)@pred(R1(jj,ii)) =
         hkey(<<kR(ii)@R1(jj',ii),pin(ii)>,TS@R1(jj',ii)>,key)).
Proof.
admit. (* TODO probably very similar to lastUpdateTag_ *)
Qed.

goal auth_R1 :
forall (jj,ii:index),
  cond@R1(jj,ii)
  =>
  (exists (j:index), T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii)).
Proof.
intros.
expand cond@R1(jj,ii).
euf M0.
admit. (* ??? *)

apply lastUpdatePredR1 to jj,ii.
case H0.
apply stateReaderInit to ii.
assert <<kR(ii1)@pred(R1(jj1,ii1)),pin(ii1)>,TS@pred(R1(jj1,ii1))> = idinit(ii).
fresh M4.
apply hashNotPair to
  <<kR(ii)@R1(jj',ii),pin(ii)>,TS@R1(jj',ii)>,
  <kR(ii1)@pred(R1(jj1,ii1)),pin(ii1)>,
  TS@pred(R1(jj1,ii1)).

apply lastUpdatePredR1 to jj,ii.
case H0.
apply stateReaderInit to ii.
assert <kR(ii1)@pred(R1(jj1,ii1)),pin(ii1)> = idinit(ii).
fresh M4.
apply hashNotPair to
  <<kR(ii)@R1(jj',ii),pin(ii)>,TS@R1(jj',ii)>,
  kR(ii1)@pred(R1(jj1,ii1)),
  pin(ii1).

assert (i=ii || i<>ii).
case H0.
(* case i=ii - honest case *)
exists j.
(* case i<>ii - absurd, we derive a contradiction *)
apply lastUpdateT to i,j.
apply lastUpdatePredR1 to jj,ii.
case H0.
(* init case *)
apply stateTagInit to i.
apply stateReaderInit to ii.
case H0.
assert hkey(<<kR(ii)@R1(jj',ii),pin(ii)>,TS@R1(jj',ii)>,key) = idinit(i).
fresh M6.
(* general case *)
case H0.
apply stateReaderInit to ii.
assert idinit(ii) = hkey(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key).
fresh M5.
assert
  hkey(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key) =
  hkey(<<kR(ii)@R1(jj',ii),pin(ii)>,TS@R1(jj',ii)>,key).
collision.

apply lastUpdatePredR1 to jj,ii.
case H0.
apply stateReaderInit to ii.
assert <<fst(kT(i)@pred(T1(i,j))),pin(i)>,snd(input@T(i,j))> = idinit(ii).
fresh M4.
apply hashNotPair to 
  <<kR(ii)@R1(jj',ii),pin(ii)>,TS@R1(jj',ii)>,
  <fst(kT(i)@pred(T1(i,j))),pin(i)>,
  snd(input@T(i,j)).
Qed.

goal auth_T1 :
forall (i,j:index),
  cond@T1(i,j)
  =>
  (exists (jj:index), R1(jj,i) < T1(i,j) && output@R1(jj,i) = input@T1(i,j)).
Proof.
intros.
expand cond@T1(i,j).
euf M0.
admit. (* ??? *)
apply lastUpdatePredT1 to i,j.
case H0.
(* case init *)
apply stateTagInit to i.
assert idinit(i) = <kR(ii)@pred(R1(jj,ii)),pin(ii)>.
fresh M4.
(* general case *)
assert 
  hkey(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key) =
  <kR(ii)@pred(R1(jj,ii)),pin(ii)>.
apply hashNotPair to
  <<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,
  kR(ii)@pred(R1(jj,ii)),
  pin(ii).
exists jj.

apply lastUpdateT to i1,j1.
case H0.
apply stateTagInit to i1.
assert idinit(i1) = <fst(kT(i)@pred(T1(i,j))),pin(i)>.
fresh M4.
assert
  hkey(<<fst(kT(i1)@pred(T1(i1,j'))),pin(i1)>,snd(input@T(i1,j'))>,key) =
  <fst(kT(i)@pred(T1(i,j))),pin(i)>.
apply hashNotPair to
  <<fst(kT(i1)@pred(T1(i1,j'))),pin(i1)>,snd(input@T(i1,j'))>,
  fst(kT(i)@pred(T1(i,j))),
  pin(i).

apply lastUpdatePredT1 to i,j.
case H0.
(* case init *)
apply stateTagInit to i.
assert idinit(i) = <fst(kT(i1)@pred(T1(i1,j1))),pin(i1)>.
fresh M4.
(* general case *)
assert 
  hkey(<<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,key) =
  <fst(kT(i1)@pred(T1(i1,j1))),pin(i1)>.
apply hashNotPair to
  <<fst(kT(i)@pred(T1(i,j'))),pin(i)>,snd(input@T(i,j'))>,
  fst(kT(i1)@pred(T1(i1,j1))),
  pin(i1).
Qed.
