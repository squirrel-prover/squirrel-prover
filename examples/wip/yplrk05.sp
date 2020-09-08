(*******************************************************************************
YPLRK05

T. van Deursen and S. Radomirović, ‘Attacks on RFID Protocols’,
Cryptology ePrint Archive, vol. 2008, no. 310, pp. 1–56, Aug. 2009.

The reader and tag share secrets k, k1, k2.
The reader initiates the protocol by challenging the tag with a nonce r1.
The tag responds with h(k1 XOR r1 XOR k).
The reader then replies with h(k2) and both tag and reader update secrets k1 and
k2.
*******************************************************************************)

hash h

abstract ok : message
abstract error : message

name seed1 : index->message
name seed2 : index->message
name key : index->message
name k : index->message
name r1 : index->message

mutable kT : index->message
mutable kR : index->message

channel cT
channel cR

axiom stateTagInit : forall (i:index), kT(i)@init = < seed1(i), seed2(i) >
axiom stateReaderInit : forall (ii:index), kR(ii)@init = < seed1(ii), seed2(ii) >

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, xr1);
  out(cT, h(fst(kT(i)) XOR xr1 XOR k(i), key(i)));
  in(cR, xh2);
  if xh2 = h(snd(kT(i)), key(i)) then
    kT(i) := < fst(kT(i)) XOR h(snd(kT(i)), key(i)),
               snd(kT(i)) XOR h(fst(kT(i)) XOR xr1 XOR k(i), key(i)) >;
    out(cT, ok)
  else
    out(cT, error)

(* jj = generic reader's session *)
process reader(jj:index) =
  out(cR, r1(jj));
  in(cT, xh1);
  (* in conditional and output terms, we would like kR(ii) before update *)
  try find ii such that xh1 = h(fst(kR(ii)) XOR r1(jj) XOR k(ii), key(ii)) in
    kR(ii) := < fst(kR(ii)) XOR h(snd(kR(ii)), key(ii)),
                snd(kR(ii)) XOR h(fst(kR(ii)) XOR r1(jj) XOR k(ii), key(ii)) >;
    out(cT, h(snd(kR(ii),key(ii))
  else
    out(cT, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).
