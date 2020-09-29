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

(* First attempt at writing a lemma about tag's state value *)
(* There is actually one case for which it is false *)
goal updateTag :
forall (t:timestamp), forall (i,j:index), (t >= T(i,j) && t < T1(i,j)) => kT(i)@T(i,j) = kT(i)@t.
Proof.
induction.
case t. case H0.

apply IH0 to pred(R(jj)). apply H0 to i,j.
apply IH0 to pred(R1(jj,ii)). apply H0 to i,j.
apply IH0 to pred(R2(jj)). apply H0 to i,j.

assert T(i1,j1) = T(i,j) || T(i1,j1) > T(i,j).
case H0.
apply IH0 to pred(T(i1,j1)). apply H0 to i,j. 

assert i=i1 || i<>i1. case H0.
assert j=j1 || j<>j1. case H0.
apply IH0 to pred(T1(i,j1)). apply H0 to i,j.
admit. (* lemma false in this case *)

assert kT(i)@T1(i1,j1) = kT(i)@pred(T1(i1,j1)).
admit. (* missing tactic to reason on the conditional in D1 ? *)
admit.

apply IH0 to pred(T2(i1,j1)). apply H0 to i,j.
Qed.

(* Another lemma, seems to hold, but not yet proved *)
goal lastUpdate : forall (t:timestamp), forall (i:index)
  (kT(i)@t = kT(i)@init && forall (j':index) t < T(i,j')) 
  ||
  (exists j:index,
   kT(i)@t = kT(i)@T(i,j) &&
   T(i,j) <= t && t < T1(i,j) &&
   (forall (j':index), T1(i,j') <= T(i,j) || t < T1(i,j'))).
Proof.
admit.
Qed.

goal auth_R1_induction :
forall (t:timestamp), forall (jj,ii:index),
  (t = R1(jj,ii) && exec@t) (* exec@t (not only cond@t) is needed in the proof *)
  =>
  (exists (j:index), T(ii,j) < t && output@T(ii,j) = input@t).
Proof.
induction.
substitute t,R1(jj,ii).
expand exec@R1(jj,ii). expand cond@R1(jj,ii).
euf M0.

  (* case 1/3: equality with hashed message in update@R1 *)
  assert (R1(jj1,ii) = R1(jj,ii) || R1(jj1,ii) < R1(jj,ii)).
  case H1.
  case H2.
    (* case R1(jj1,ii) = R1(jj,ii) *)
    admit. (* ??? *)
    (* this equality is legitimate, but I don't see how to deal with it for the proof *)
    (* case R1(jj1,ii) < R1(jj,ii) *)
    apply IH0 to R1(jj1,ii).
    executable pred(R1(jj,ii)).
    apply H3 to R1(jj1,ii).
    apply H2 to jj1,ii.
    expand exec@R1(jj1,ii). expand cond@R1(jj1,ii).
    exists j.

  (* case 2/3: equality with hashed message in output@T *)
  (* honest case *)
  assert T(ii,j) < R1(jj,ii). case H1.
  exists j.

  (* case 3/3: equality with hashed message in update@T1 *)
  (* if there is an update@T1, then action T happened before *)
  assert T1(ii,j) < R1(jj,ii). case H1.
  (* here, I use updateTag but actually the lemma is not always true *)
  (* I think I should use lastUpdate instead (or a similar lemma), 
  but I have not yet managed to do so *)
  apply updateTag to pred(T1(ii,j)).
  depends T(ii,j),T1(ii,j).
  apply H2 to ii,j.
  exists j.
Qed.
