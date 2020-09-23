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

hash h1
hash h2

abstract ok : message
abstract error : message

name seed1 : index->message
name seed2 : index->message
name key1 : index->message
name key2 : index->message
name k : index->message
name r1 : index->message

mutable kT : index->message (* <<k1_old,k2_old>,<k1,k2>> *)
mutable kR : index->message (* <<k1_old,k2_old>,<k1,k2>> *)

channel cT
channel cR

axiom stateTagInit :
  forall (i:index),
    kT(i)@init = << seed1(i), seed2(i) >, < seed1(i), seed2(i) >>
axiom stateReaderInit :
  forall (ii:index),
    kR(ii)@init = << seed1(ii), seed2(ii) >, < seed1(ii), seed2(ii) >>

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, xr1);
  out(cT, h1(fst(snd(kT(i))) XOR xr1 XOR k(i), key1(i)));
  in(cR, xh2);
  if xh2 = h2(snd(fst(kT(i))), key2(i)) then
    kT(i) := < snd(kT(i)),
               < fst(snd(kT(i))) XOR h2(snd(snd(kT(i))), key2(i)),
                 snd(snd(kT(i))) XOR h1(fst(snd(kT(i))) XOR xr1 XOR k(i), key1(i)) >>;
    out(cT, ok)
  else
    out(cT, error)

(* jj = generic reader's session *)
process reader(jj:index) =
  out(cR, r1(jj));
  in(cT, xh1);
  try find ii such that xh1 = h1(fst(fst(kR(ii))) XOR r1(jj) XOR k(ii), key1(ii)) in
    kR(ii) := < snd(kR(ii)),
                < fst(snd(kR(ii))) XOR h2(snd(snd(kR(ii))), key2(ii)),
                  snd(snd(kR(ii))) XOR h1(fst(snd(kR(ii))) XOR r1(jj) XOR k(ii), key1(ii)) >>;
    out(cT, h2(snd(fst(kR(ii))),key2(ii)))
  else
    out(cT, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).

goal stateIncrease :
forall (jj,jj',ii:index), R1(jj',ii) < R1(jj,ii) => kR(ii)@R1(jj',ii) <> kR(ii)@R1(jj,ii). 
Proof.
admit.
Qed.

goal auth_R1 :
forall (jj,ii:index),
  cond@R1(jj,ii) =>
  (exists (j:index), T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii)).
Proof.
intros.
expand cond@R1(jj,ii).
euf M0.

(* case equality with hashed message in update@R1 *)
assert (R1(jj1,ii) = R1(jj,ii) || R1(jj1,ii) < R1(jj,ii)).
case H0.
case H1.
(* case R1(jj1,ii) = R1(jj,ii) *)
assert snd(kR(ii)@pred(R1(jj,ii))) = fst(kR(ii)@R1(jj,ii)).
admit. (* TODO ??? *)
(* case R1(jj1,ii) < R1(jj,ii) *)
(* use freshness of r1 and stateIncrease to conclude the equality cannot hold ? *)
apply stateIncrease to jj,jj1,ii.
admit. (* TODO ??? *)

(* case equality with hashed message in output@T *)
(* honest case *)
assert T(ii,j) < R1(jj,ii). case H0.
exists j.

(* case equality with hashed message in update@T1 *)
(* if there is an update@T1, then action T happened before *)
assert T1(ii,j) < R1(jj,ii). case H0.
assert input@T(ii,j) = r1(jj). admit. (* TODO ??? *)
assert input@R1(jj,ii) = h1(xor(xor(fst(snd(kT(ii)@T(ii,j))),input@T(ii,j)),k(ii)),key1(ii)). admit. (* TODO ??? *)
depends T(ii,j),T1(ii,j).
exists j.
Qed.
