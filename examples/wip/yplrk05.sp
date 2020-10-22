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

(* WARNING *)
(* Until the semantics is fixed in the tool, a state macro s@t is interpreted:
    - by the value AFTER the update for occurrences in output, cond terms,
    - by the value BEFORE the update for occurrences in update term.
   This is why we store in the state both old and current values. *)

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

(* Assumption on the sequentiality of the sessions for a given tag's id *)
axiom sequentiality :
  forall (t:timestamp), forall (i,j:index),
    T(i,j) < t && t < T1(i,j) => not(exists (j':index), t = T1(i,j') && j <> j')

system [sequence] null.

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
(* case i=i1 && j<>j1 *)
apply sequentiality to t. apply H0 to i,j. exists j1.
(* case i<>i1 *)
apply IH0 to pred(T1(i1,j1)). apply H0 to i,j.
assert kT(i)@T1(i1,j1) = kT(i)@pred(T1(i1,j1)).
case (if i = i1 then
       <snd(kT(i1)@pred(T1(i1,j1))),
        <xor(fst(snd(kT(i1)@pred(T1(i1,j1)))),
             h2(snd(snd(kT(i1)@pred(T1(i1,j1)))),key2(i1))),
         xor(snd(snd(kT(i1)@pred(T1(i1,j1)))),
             h1(xor(xor(fst(snd(kT(i1)@pred(T1(i1,j1)))),input@T(i1,j1)),
                    k(i1)),key1(i1)))>>
       else kT(i)@pred(T1(i1,j1))).

apply IH0 to pred(T2(i1,j1)). apply H0 to i,j.
Qed.

goal auth_R1_induction_weak :
forall (t:timestamp), forall (jj,ii:index),
  (t = R1(jj,ii) && exec@t) (* exec@t (not only cond@t) is needed in the proof *)
  =>
  (exists (j:index), T(ii,j) < t && output@T(ii,j) = input@t).
Proof.
induction.
substitute t,R1(jj,ii).
expand exec@R1(jj,ii). expand cond@R1(jj,ii).
assert input@R1(jj,ii) = h1(xor(xor(fst(snd(kR(ii)@pred(R1(jj,ii)))),r1(jj)),k(ii)),key1(ii)).
(* M0 and M1 are "equivalent" but it helps the proof to apply euf on M1
(that contains pred(R1(jj,ii))) and not on M0 (that contains R1(jj,ii))
because we only have to consider timestamps t < R1(jj,ii) *)
euf M1.

  (* case 1/3: equality with hashed message in update@R1 *)
  apply IH0 to R1(jj1,ii).
  executable pred(R1(jj,ii)).
  apply H2 to R1(jj1,ii).
  apply H1 to jj1,ii.
  expand exec@R1(jj1,ii). expand cond@R1(jj1,ii).
  exists j.

  (* case 2/3: equality with hashed message in output@T *)
  (* honest case *)
  exists j.

  (* case 3/3: equality with hashed message in update@T1 *)
  (* if there is an update@T1, then action T happened before *)
  apply updateTag to pred(T1(ii,j)).
  depends T(ii,j),T1(ii,j).
  apply H1 to ii,j.
  exists j.
Qed.

goal auth_T1_induction_weak :
forall (t:timestamp), forall (i,j:index),
  (t = T1(i,j) && exec@t) (* exec@t (not only cond@t) is needed in the proof *)
  =>
  (exists (jj:index),
   R1(jj,i) < t &&
   output@R1(jj,i) = input@t).
Proof.
induction.
substitute t,T1(i,j).
expand exec@T1(i,j). expand cond@T1(i,j).
assert input@T1(i,j) = h2(snd(snd(kT(i)@pred(T1(i,j)))),key2(i)).
euf M1.

  (* case 1/3: equality with hashed message in output@R1 *)
  (* honest case *)
  exists jj.

  (* case 2/3: equality with hashed message in update@R1 *)
  (* honest case *)
  exists jj.

  (* case 3/3: equality with hashed message in update@T1 *)
  apply IH0 to T1(i,j1).
  executable pred(T1(i,j)).
  apply H2 to T1(i,j1).
  apply H1 to i,j1.
  expand exec@T1(i,j1). expand cond@T1(i,j1).
  exists jj.
Qed.
