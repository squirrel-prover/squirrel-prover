(*******************************************************************************
YPLRK05

T. van Deursen and S. Radomirović, ‘Attacks on RFID Protocols’,
Cryptology ePrint Archive, vol. 2008, no. 310, pp. 1–56, Aug. 2009.

The reader and tag share secrets k, k1, k2.
The reader initiates the protocol by challenging the tag with a nonce r1.
The tag responds with h(k1 XOR r1 XOR k).
The reader then replies with h(k2) and both tag and reader update secrets k1 and
k2.

In this model we use 2 different keyed hash functions, instead of a single (not
keyed) hash function as in the specification.

R -> T : r1
T -> R : h(kT1+r1+k)
         kT1 := k1+h(k2)
         kT2 := k2+h(k1+r1+k)
R -> T : h(kR2)
         kR1 := k1+h(k2)
         kR2 := k2+h(k1+r1+k)
*******************************************************************************)

(*******************************************************************************
Here, we try to prove that we can replace the last output of the reader
by a nonce.
*******************************************************************************)

hash h1
hash h2

abstract ok : message
abstract error : message

name key1 : index->message
name key2 : index->message
name k : index->message
name r1 : index->message

name k1init : index->message
name k2init : index->message

mutable kT(i:index) : message = <k1init(i),k2init(i)>
mutable kR(ii:index) : message = <k1init(ii),k2init(ii)>

channel cT
channel cR

name nR : index->index->message

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, xr1);
  out(cT, h1(fst(kT(i)) XOR xr1 XOR k(i), key1(i)));
  in(cR, xh2);
  if xh2 = h2(snd(kT(i)), key2(i)) then
    kT(i) := < fst(kT(i)) XOR h2(snd(kT(i)), key2(i)),
               snd(kT(i)) XOR h1(fst(kT(i)) XOR xr1 XOR k(i), key1(i)) >;
    out(cT, ok)
  else
    out(cT, error)

(* jj = generic reader's session *)
process reader(jj:index) =
  out(cR, r1(jj));
  in(cT, xh1);
  try find ii such that xh1 = h1(fst(kR(ii)) XOR r1(jj) XOR k(ii), key1(ii)) in
    let m = h2(snd(kR(ii)),key2(ii)) in
    kR(ii) := < fst(kR(ii)) XOR h2(snd(kR(ii)), key2(ii)),
                snd(kR(ii)) XOR h1(fst(kR(ii)) XOR r1(jj) XOR k(ii), key1(ii)) >;
    out(cT, diff(m,nR(jj,ii)))
  else
    out(cT, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).

(* Minimal sequentiality assumption needed for the proofs *)
axiom sequentiality :
  forall (t:timestamp), forall (i,j:index),
    happens(T(i,j),t,T1(i,j)) =>
    (T(i,j) < t && t < T1(i,j) => not(exists (j':index), t = T1(i,j') && j <> j')).

equiv outputReader.
Proof.
induction t.

(* case t = R(jj) *)
expandall.
fa 0. fa 1. fa 1.
fresh 1.
yesif 1.
split.
assert happens(R2(jj1)). by depends R(jj1),R2(jj1). 
assert happens(R1(jj1,ii)). by depends R(jj1),R1(jj1,ii).

(* case t = R1(jj,ii) *)
expandall.
fa 0. fa 1. fa 2.
(* output@R1(jj,ii) *)
prf 2.
yesif 2.
split.
(* case prf: equality with h2 in T1(i,j) *)
admit. (* ??? we need to reason on state (de)synchronization ??? *)
(* case prf: equality with h2 in R1(jj1,ii1) *)
admit. (* ok, state invariant *)
fresh 2.
yesif 2.
(* cond@R1(jj,ii) *)
equivalent
  (input@R1(jj,ii) = h1(xor(xor(fst(kR(ii)@pred(R1(jj,ii))),r1(jj)),k(ii)),key1(ii))),
  (exists (j:index), T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii)).
admit. (* ??? can we use auth ??? *)
by fadup 1.

(* case t = R2(jj) *)
expandall.
admit. (* ??? can we use auth ??? *)

(* case t = T(i,j) *)
expandall.
fa 0. fa 1. fa 1.
prf 1.
yesif 1.
split.
admit. (* ??? *)
(* it seems to me that the previous case is possible: if T(i,j1) aborts,
then values of kT(i) is the same @T(i,j1) and @T(i,j),
and we could have input@T(i,j) = input@T(i,j1)  *)
(* so I don't see how we could derive False *)
admit. (* ??? *)
by fresh 1.

(* case t = T1(i,j) *)
expandall.
fa 0. fa 1.
admit. (* ??? can we use auth ??? *)

(* case t = T2(i,j) *)
expandall.
fa 0. fa 1.
admit. (* ??? can we use auth ??? *)
Qed.
