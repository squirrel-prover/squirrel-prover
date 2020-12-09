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

mutable kT : index->message (* <k1,k2> *)
mutable kR : index->message (* <k1,k2> *)

channel cT
channel cR

axiom stateTagInit :
  forall (i:index),
    kT(i)@init = < seed1(i), seed2(i) >
axiom stateReaderInit :
  forall (ii:index),
    kR(ii)@init = < seed1(ii), seed2(ii) >

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

(* Minimal sequentiality assumption needed for the proofs *)
axiom sequentiality :
  forall (t:timestamp), forall (i,j:index),
    T(i,j) < t && t < T1(i,j) => not(exists (j':index), t = T1(i,j') && j <> j')

(* "Empty" system, useful only to define the axiom sequentiality
   where we need to talk about actions T(i,j) and T1(i,j), which
   are defined only after the previous system *)
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
       <xor(fst(kT(i1)@pred(T1(i1,j1))),
            h2(snd(kT(i1)@pred(T1(i1,j1))),key2(i1))),
        xor(snd(kT(i1)@pred(T1(i1,j1))),
            h1(xor(xor(fst(kT(i1)@pred(T1(i1,j1))),input@T(i1,j1)),k(i1)),
               key1(i1)))>
       else kT(i)@pred(T1(i1,j1))).

apply IH0 to pred(T2(i1,j1)). apply H0 to i,j.
Qed.

goal readerUpdateTerm :
  forall (jj,ii:index),
  kR(ii)@R1(jj,ii) =
    < fst(kR(ii)@pred(R1(jj,ii))) XOR h2(snd(kR(ii)@pred(R1(jj,ii))), key2(ii)),
      snd(kR(ii)@pred(R1(jj,ii)))
        XOR h1(fst(kR(ii)@pred(R1(jj,ii))) XOR r1(jj) XOR k(ii), key1(ii)) >.
Proof.
simpl.
Qed.

goal auth_R1_weak :
forall (jj,ii:index),
  cond@R1(jj,ii)
  =>
  (exists (j:index), T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii)).
Proof.
intros.
expand cond@R1(jj,ii).
euf M0.

  (* case 1/3: equality with hashed message in update@R1 *)
  (* this case is easily handled in the version with induction
  (see auth_R1_induction_weak) because the induction hypothesis
  allows to conclude using only the fact that R1(jj1,ii) < R1(jj,ii),
  we do not have to exploit the equality hypothesis generated by the
  euf tactic *)
  (* here, without the induction, we have to find another way to conclude *)

  assert
    input@R1(jj,ii) =
      h1(xor(xor(fst(kR(ii)@pred(R1(jj1,ii))),r1(jj1)),k(ii)),key1(ii)).
  euf M2. (* here again, we have 3 different cases *)

    (* case 1/3: equality with hashed message in update@R1 *)
    admit. (* TODO ??? *)

    (* case 2/3: equality with hashed message in output@T *)
    (* honest case *)
    exists j. case H0.

    (* case 3/3: equality with hashed message in update@T1 *)
    (* if there is an update@T1, then action T happened before *)
    apply updateTag to pred(T1(ii,j)).
    depends T(ii,j),T1(ii,j).
    apply H1 to ii,j.
    exists j.
    case H0.

  (* case 2/3: equality with hashed message in output@T *)
  (* honest case *)
  exists j.

  (* case 3/3: equality with hashed message in update@T1 *)
  (* if there is an update@T1, then action T happened before *)
  apply updateTag to pred(T1(ii,j)).
  depends T(ii,j),T1(ii,j).
  apply H0 to ii,j.
  exists j.
Qed.

(* Same goal as before, but trying a different proof *)
goal auth_R1_weak_bis :
forall (jj,ii:index),
  exec@R1(jj,ii)
  =>
  (exists (j:index), T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii)).
Proof.
intros.
expand exec@R1(jj,ii). expand cond@R1(jj,ii).
euf M0.

  (* case 1/3: equality with hashed message in update@R1 *)
  (* this case is easily handled in the version with induction
  (see auth_R1_induction_weak) because the induction hypothesis
  allows to conclude using only the fact that R1(jj1,ii) < R1(jj,ii),
  we do not have to exploit the equality hypothesis generated by the
  euf tactic *)
  (* here, without the induction, we have to find another way to conclude *)

  (* assume that R1(jj1,ii) < R1(jj,ii) and that no other R1(jj',ii)
  happens in-between => TODO handle general case *)
  assert
    kR(ii)@pred(R1(jj,ii)) =
      < fst(kR(ii)@pred(R1(jj1,ii))) XOR h2(snd(kR(ii)@pred(R1(jj1,ii))), key2(ii)),
        snd(kR(ii)@pred(R1(jj1,ii))) XOR h1(fst(kR(ii)@pred(R1(jj1,ii))) XOR r1(jj) XOR k(ii), key1(ii)) >.
  admit.
  (* assume that there is no update of kR(ii) between R(jj1)and R1(jj1,ii)
  TODO handle general case *)
  assert kR(ii)@pred(R1(jj1,ii)) = kR(ii)@pred(R(jj1)).
  admit.
  (* we can deduce the following equality *)
  assert h2(snd(kR(ii)@pred(R(jj1))),key2(ii)) = r1(jj1) XOR r1(jj).
  euf M4.
  admit. (* TODO use the fact that state increases to show that M5 is false ? *)
  depends T(ii,j),T1(ii,j). depends R(jj1),R1(jj1,ii).
  exists j.
  apply readerUpdateTerm to jj,ii.
  apply readerUpdateTerm to jj1,ii.
  assert fst(kR(ii)@pred(R1(jj,ii))) = fst(kR(ii)@R1(jj1,ii)).
  executable pred(R1(jj,ii)).
  apply H1 to R1(jj1,ii).
  expand exec@R1(jj1,ii). expand cond@R1(jj1,ii).
  admit. (* TODO ??? *)

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

goal auth_R1_induction_weak :
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
euf M0.

  (* case 1/2: equality with hashed message in output@R1 *)
  (* honest case *)
  exists jj.

  (* case 2/2: equality with hashed message in update@T1 *)
  apply IH0 to T1(i,j1).
  executable pred(T1(i,j)).
  apply H2 to T1(i,j1).
  apply H1 to i,j1.
  expand exec@T1(i,j1). expand cond@T1(i,j1).
  exists jj.
Qed.
