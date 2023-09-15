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

COMMENTS
- In this model we use 3 different keyed hash functions, instead of a single
(not keyed) hash function as in the specification.

SECURITY PROPERTIES
- authentication (reader and tag)
*******************************************************************************)

hash h
hash h1
hash h2
hash h3

abstract ok : message
abstract error : message

abstract TSinit : message
abstract TSorderOk : message
abstract TSorder : message * message -> message
abstract TSnext : message -> message

name k : message

name key1 : index -> message
name key2 : index -> message
name key3 : index -> message
name pin : index -> message
name idinit : index -> message

mutable kT(i:index) : message = <idinit(i),TSinit>
mutable kR(ii:index) : message = idinit(ii)
mutable TS : message = TSinit

channel cT
channel cR

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, x1);
  if fst(x1) = h(snd(x1),k) && TSorder(snd(kT(i)),snd(x1)) = TSorderOk then
    (out(cT, h1(fst(kT(i)),key1(i)));
    in(cR, x3);
    if x3 = h2(<fst(kT(i)),pin(i)>,key2(i)) then
      (kT(i) := <h3(<<fst(kT(i)),pin(i)>,snd(x1)>,key3(i)), snd(x1)>;
      out(cT, ok))
    else
      out(cT, error))
  else
    out(cT, error)

(* jj = generic reader's session *)
process reader(jj:index) =
  TS := TSnext(TS);
  out(cR, <h(TS,k),TS>);
  in(cT, x2);
  try find ii such that x2 = h1(kR(ii), key1(ii)) in
    let m = h2(<kR(ii),pin(ii)>,key2(ii)) in
    kR(ii) := h3(<<kR(ii),pin(ii)>,TS>,key3(ii));
    out(cR, m)
  else
    out(cR, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).

(* SECURITY PROPERTIES *)

lemma auth_R1 (jj,ii:index):
  happens(R1(jj,ii)) =>
  cond@R1(jj,ii) =>
  exists (j:index),
    T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii).
Proof.
  intro Hap @/cond Hcond.
  euf Hcond.
  intro [j _].
  by exists j.
Qed.

lemma auth_T1 (i,j:index):
  happens(T1(i,j)) =>
  cond@T1(i,j) =>
  exists (jj:index),
    R1(jj,i) < T1(i,j) && output@R1(jj,i) = input@T1(i,j).
Proof.
  intro Hap @/cond Hcond.
  euf Hcond.
  intro [jj _].
  by exists jj.
Qed.
