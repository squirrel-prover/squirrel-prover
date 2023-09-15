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
axiom sequentiality (t:timestamp, i,j:index):
  happens(T(i,j),t,T1(i,j)) =>
    T(i,j) < t => t < T1(i,j) =>
      not(exists (j':index), t = T1(i,j') && j <> j').

(* LIBRARIES *)

include Basic.

(* HELPING LEMMAS *)

lemma noUpdateTag (t:timestamp, i,j:index):
    happens(T(i,j),t,T1(i,j)) =>
      (t >= T(i,j) && t < T1(i,j)) => kT(i)@T(i,j) = kT(i)@t.
Proof.
  generalize i j.
  induction t => t IH0 i j Hap [H1 H2].
  case t => He;
  try by (repeat destruct He as [_ He]; expand kT(i)@t; apply IH0).

  auto.

  destruct He as [i0 j0 He].
  assert T(i0,j0) = T(i,j) || T(i0,j0) > T(i,j) as H0 by constraints.

  case H0; 1: auto.
  expand kT(i)@t; by apply IH0.

  destruct He as [i0 j0 He].
  rewrite He.
  case (i=i0) => _.
  case (j=j0) => _.

    (* case i=i0 && j=j0 *)
    auto.

    (* case i=i0 && j<>j0 *)
    use sequentiality with T1(i,j0),i,j => //.
    by exists j0.

    (* case i<>i0 *)
    use IH0 with pred(T1(i0,j0)),i,j as Meq; 2,3,4: auto.
    by rewrite /kT if_false //.
Qed.

(* SECURITY PROPERTIES *)

lemma auth_R1_induction (t:timestamp, jj,ii:index):
  happens(R1(jj,ii)) =>
    t = R1(jj,ii) && exec@t (* exec@t (not only cond@t) is needed *)
    =>
    exists (j:index), T(ii,j) < t && output@T(ii,j) = input@t.
Proof.
  generalize jj ii.
  induction t => t IH0 jj ii Hap [Ht0 Hexec].
  rewrite Ht0 in *; clear Ht0.

  expand exec, cond.
  destruct Hexec as [H1 Meq].
  euf Meq.

    (* case 1/3: equality with hashed message in update@R1 *)
  + intro [jj0 [Ht Heq]].
    executable pred(R1(jj,ii)) => // H.
    use H with R1(jj0,ii) as Ht1; 2: auto.
    expand exec, cond.
    destruct Ht1 as [_ _].
    use IH0 with R1(jj0,ii),jj0,ii as [j _]; 2,3,4: auto.
    by exists j.

    (* case 2/3: equality with hashed message in output@T *)
    (* honest case *)
  + by intro [j _]; exists j.

    (* case 3/3: equality with hashed message in update@T1 *)
    (* if there is an update@T1, then action T happened before *)
  + intro [j [Ht Heq]].
    exists j.
    depends T(ii,j),T1(ii,j) by auto => _.
    by rewrite /output (noUpdateTag (pred(T1(ii,j)))).
Qed.

lemma auth_T1_induction (t:timestamp, i,j:index):
  happens(t) =>
    t = T1(i,j) && exec@t (* exec@t (not only cond@t) is needed *)
    =>
    exists (jj:index), R1(jj,i) < t && output@R1(jj,i) = input@t.
Proof.
  generalize i j.
  induction t => t IH0 i j Hap [Ht Hexec].
  rewrite Ht in *; clear Ht.

  rewrite /exec /cond in Hexec.
  destruct Hexec as [H1 Meq].
  euf Meq => [jj [Clt H]]. 

    (* case 1/3: equality with hashed message in output@R1 *)
    (* honest case *)
  + by exists jj.

    (* case 3/3: equality with hashed message in update@T1 *)
  +  use IH0 with T1(i,jj), i, jj as [jjj [_ H2]] => //. {
     exists jjj => /=.
     rewrite H2 Meq H. 
     executable pred(T1(i,j)); try auto. 
     intro H3.
     by apply H3 in Clt.
    } 

    simpl.
    executable pred(T1(i,j)) => // H3.
    by apply H3.
Qed.
