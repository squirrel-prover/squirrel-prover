(*******************************************************************************
YPLRK05

T. van Deursen and S. Radomirović, ‘Attacks on RFID Protocols’,
Cryptology ePrint Archive, vol. 2008, no. 310, pp. 1–56, Aug. 2009.

The reader and tag share secrets k, k1, k2.
The reader initiates the protocol by challenging the tag with a nonce r1.
The tag responds with h(k1 XOR r1 XOR k).
The reader then replies with h(k2) and both tag and reader update secrets k1 and
k2.

R -> T : r1
T -> R : h(kT1+r1+k)
         kT1 := kT1+h(kT2)
         kT2 := kT2+h(kT1+r1+k)
R -> T : h(kR2)
         kR1 := kR1+h(kR2)
         kR2 := kR2+h(kR1+r1+k)

COMMENTS
- In this model we use 2 different keyed hash functions, instead of a single
(not keyed) hash function as in the specification.

HELPING LEMMAS
- no update

SECURITY PROPERTIES
- authentication
*******************************************************************************)

hash h1
hash h2

abstract ok : message
abstract error : message

name key1 : index -> message
name key2 : index -> message
name k : index -> message
name r1 : index -> message

name k1init : index -> message
name k2init : index -> message

mutable kT(i:index) : message = <k1init(i),k2init(i)>
mutable kR(i:index) : message = <k1init(i),k2init(i)>

channel cT
channel cR

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
    out(cT, m)
  else
    out(cT, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).

(* AXIOMS *)

(* Minimal sequentiality assumption needed for the proofs *)
axiom  sequentiality (t:timestamp, i,j:index):
  happens(T(i,j),t,T1(i,j)) =>
    T(i,j) < t => t < T1(i,j) =>
      not(exists (j':index), t = T1(i,j') && j <> j').



(* LIBRARIES *)

include Core.

(* HELPING LEMMAS *)

lemma noUpdateTag (t:timestamp, i,j:index):
    happens(T(i,j),t,T1(i,j)) =>
      (t >= T(i,j) && t < T1(i,j)) => kT(i)@T(i,j) = kT(i)@t.
Proof.
  induction t.
  use sequentiality.
  smt ~steps:35744.
Qed.

(* SECURITY PROPERTIES *)

lemma auth_R1_induction (t:timestamp, jj,ii:index):
  happens(R1(jj,ii)) =>
    t = R1(jj,ii) && exec@t (* exec@t (not only cond@t) is needed *)
    =>
    exists (j:index), T(ii,j) < t && output@T(ii,j) = input@t.
Proof.
  use noUpdateTag.
  generalize jj ii.
  induction t => t IH0 ii jj Hap [Ht0 Hexec].
  destruct Hexec as [_ Meq].
  euf Meq; smt ~prover:CVC5 ~steps:138919.
Qed.

lemma auth_T1_induction (t:timestamp, i,j:index):
  happens(t) =>
    t = T1(i,j) && exec@t (* exec@t (not only cond@t) is needed *)
    =>
    exists (jj:index), R1(jj,i) < t && output@R1(jj,i) = input@t.
Proof.
  generalize i j.
  induction t => t IH0 i j Hap [Ht Hexec].
  destruct Hexec as [H1 Meq].
  euf Meq; smt ~prover:CVC5 ~steps:60310.
Qed.
