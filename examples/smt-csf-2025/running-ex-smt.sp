(*******************************************************************************
RUNNING EXAMPLE

This protocol is a variant of the OSK protocol described in:
M. Ohkubo, K. Suzuki, S. Kinoshita et al.,
“Cryptographic approach to “privacy-friendly” tags,”
RFID privacy workshop, vol. 82. Cambridge, USA, 2003.

Each tag is associated to a mutable state sT initialized with s0.
Readers have access to a database containing an entry sR for each authorized
tag.

         sT := H(sT,k)
T -> R : G(sT,k')

         input x; sR := H(sR,k) if x = G(H(sR,k),k') with sR in DB
R -> T : ok

COMMENTS
- In this model we use two keyed hash functions H and G with fixed keys k and
k', instead of two not keyed hash functions as in the specification.
We address this issue in the file `running-ex-oracle.sp` by adding a process in
order to provide the attacker the ability to compute hashes with their
respective keys (without knowing these keys).

HELPING LEMMAS
- last update
- disjoint chains

SECURITY PROPERTIES
- authentication
*******************************************************************************)

hash H
hash G
name k : message
name k' : message
name s0 : index -> message
mutable sT(i:index) : message = s0(i)
mutable sR(i:index) : message = s0(i)

abstract ok : message
channel cT
channel cR

mutex lT:1.
mutex lR:0.

process tag(i:index) =
  lock lT(i);
  sT(i):=H(sT(i),k);
  out(cT,G(sT(i),k'));
  unlock lT(i).

process reader =
  lock lR;
  in(cT,x);
  try find ii such that x = G(H(sR(ii),k),k') in
    sR(ii):=H(sR(ii),k);
    out(cR,ok);
    unlock lR else unlock lR.

system (!_i !_j T: tag(i) | !_jj R: reader).

include Core.

(* HELPING LEMMAS *)

(* Last update lemmas: basic reasoning about the memory cells.
Each lemma has two versions, one for the tag and one for the reader.
We describe below the tag's lemmas, the reader's lemmas are similar. *)

lemma lastupdateTag (i:index,tau:timestamp):
  happens(tau) => (
    (sT(i)@tau = sT(i)@init && forall j, happens(T(i,j)) => T(i,j)>tau) ||
    (exists j,
      sT(i)@tau = sT(i)@T(i,j) && T(i,j)<=tau &&
        forall j', happens(T(i,j')) && T(i,j')<=tau => T(i,j')<=T(i,j))).
Proof.
  induction tau.
  smt ~prover:Z3 ~steps:95576.
Qed.

lemma lastupdateReader (ii:index,tau:timestamp):
  happens(tau) => (
    (sR(ii)@tau = sR(ii)@init &&
      forall jj, happens(R(jj,ii)) => R(jj,ii)>tau) ||
    (exists jj,
      sR(ii)@tau = sR(ii)@R(jj,ii) && R(jj,ii)<=tau &&
        forall jj',
          happens(R(jj',ii)) && R(jj',ii)<=tau => R(jj',ii)<=R(jj,ii))).
Proof.
induction tau.
smt ~prover:Z3 ~steps:74801.
Qed.

(* The following lemma states that values of different memory cells do not
overlap, relying on the collision resistance of the hash function. *)

lemma disjoint_chains (tau',tau:timestamp,i',i:index) :
  happens(tau',tau) =>
    i<>i' => sT(i)@tau <> sR(i')@tau'.
Proof.
  generalize tau.
  induction tau' => tau' IH tau D E Meq.
  use lastupdateTag with i,tau as [[A0 Hinit] | [j [A0 A1 Hsup]]] => //;
  use lastupdateReader with i',tau' as [[A Hinit'] | [j' [B C Hsup']]] => //.

  + rewrite -Meq A0 /sR in B.
    by fresh B.

  + rewrite Meq A /sT in A0.
    by fresh A0.

  + rewrite Meq B /sT in A0.
    expand sR(i')@R(j',i').
    collision A0 => H.
    smt ~steps:21881. 
Qed.

(* SECURITY PROPERTIES *)

lemma authentication (jj,ii:index):
   happens(R(jj,ii)) =>
   cond@R(jj,ii) =>
   exists (j:index), T(ii,j) < R(jj,ii) && output@T(ii,j) = input@R(jj,ii).
Proof.
  intro Hap @/cond Hcond.
  euf Hcond.
  intro [i j [Ht M]].
  case (i=ii) => _; 1: by exists j.
  rewrite /sT in M.
  collision.
  intro Meq.
  by use disjoint_chains with pred(R(jj,ii)),pred(T(i,j)),ii,i.
Qed.
