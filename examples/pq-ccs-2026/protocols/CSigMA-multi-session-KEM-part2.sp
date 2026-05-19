(** Long-term keys:
   - skA, skB signature keys for A and B

   Session keys:
   - A: eskA, rA
   - B: kB, r, rB

   Messages a and b are arbitrary. Various distinct tags are used.

   Transcripts:
   - t2 = [epkA,enc(kB,r,epkA)]
   - t4 = [epkA,enc(kB,r,epkA),rA,rB]

   A->B: pk(eskA) =def epkA
   B->A: enc(kB,r,epkA)
   both compute kmac = kdf(<tagmac,t2>,kB)
   A->B: rA
   B->A: b, rB, sign(<tag0,t4>,skB), mac(<tag0,b>,kmac)
   A->B: a,     sign(<tag1,t4>,skA), mac(<tag1,a>,kmac)

   Both finally compute kdf(<tagke,<<rA,rB>,<a,b>>>,kB). *)

(** Main lemma: establish Strong Secrecy of the key KeyB (as computed  by B)
   in the idealized version. We only consider one session of A
   and one session of B.
   In the idealized version the occurrences of kB in plaintext are replaced
   by kfresh.
   The proof mainly relies on prf. *)


(** -------------------------------------------------------- *)

(** ## KEM primitives, with functionality axiom and CPA game *)

(** The KEM relies on a secret/public keypair.

    The public key is generated using `kem_pub` from the secret key.

    Then `encap` is a randomized primitive (with explicit randomness
    as usual) that takes a public key and returns:
    - a shared secret 'encap_shared';
    - a public encapsulation 'encap_public'.
    The `decap` primitive then allows to recover the shared secret
    from the public encapsulation and the secret key.

    We use type `message` for the encapsulation and public keys
    to avoid conversions. *)

include Core.
include PostQuantum.
set postQuantumEquivs=true.

close Classic.
open Quantum.


type kem_skey[serializable].
type kem_randomness[serializable].
type kem_shared[serializable,large].

abstract empty_shared : kem_shared.

abstract kem_pub : kem_skey -> message.
abstract encap_shared : kem_randomness -> message -> kem_shared.
abstract encap_public : kem_randomness -> message -> message.
abstract decap : message -> kem_skey -> kem_shared.

exact axiom [any] decap_encap (r:kem_randomness,k:kem_skey) :
  decap (encap_public r (kem_pub k)) k = encap_shared r (kem_pub k).
hint rewrite decap_encap.

abstract format ['a] : 'a -> message.
abstract parse  ['a] : message -> 'a.
axiom [any] formatting_kem_randomness (x:kem_randomness) : parse (format x) = x.
axiom [any] formatting_kem_shared     (x:kem_shared)     : parse (format x) = x.

(** CPA game for KEMs as in, e.g.,
    <https://eprint.iacr.org/2020/1364.pdf> or <https://eprint.iacr.org/2018/903.pdf>.
    This corresponds to the strong secrecy of the shared secret
    `encap r (kem_pub skey) # 1` even when the public encapsulation is revealed. *)
game KEM_CPA_SINGLE = {
  rnd skey : kem_skey;
  rnd r : kem_randomness;
  rnd s : kem_shared;
  oracle o_pub = {
    return (kem_pub skey)
  }
  oracle o_encap_shared = {
    return diff(encap_shared r (kem_pub skey), s)
  }
  oracle o_encap_public = {
    return (encap_public r (kem_pub skey))
  }
}.

(** CPA game for multiple keys - stronger than the previous game *)

game KEM_CPA = {
  rnd skey : kem_skey;

  oracle o_pub = {
    return (kem_pub skey)
  }
  oracle o_encap_shared = {
    rnd r : kem_randomness;
    rnd s : kem_shared;
    return (
      encap_public r (kem_pub skey),
      diff(encap_shared r (kem_pub skey), s)
    )
  }
}.

(** ---------------------------------------------------------------------- *)
signature sign, checksign, vk.
hash kdf where k:kem_shared.
hash mac.


abstract a : message.
abstract b : message.

abstract tag1   : message.
abstract tag0   : message.
abstract tagke  : message.
abstract tagmac : message.


axiom [any] tags_neq : tag0 <> tag1.

axiom [any] tagke_tagmac_neq : tagke <> tagmac.

axiom [any] sufcma :
  forall (m,s,sk:message), checksign(m,s,vk(sk)) => s = sign(m,sk).


(** Long-term keys *)
name skA : message.
name skB : message.


(** Session keys for B. *)
name r      : index * index  -> kem_randomness.
name r'     : index -> kem_randomness.
name rB     : index -> message.
name kS: index -> message.

name kBh: index * index -> kem_shared.

channel cA.
channel cB.

(** ---------------------------------------------------------------------- *)

(** Ideal A which runs with kB if it receives kfresh *)
(** Computation of KeyA has been removed *)

(** session keys for A *)
name eskA : index -> kem_skey.
name rA : index -> message.
process A_ideal_normal(i:index) =
  let epkA = kem_pub (eskA i) in
  out(cA, epkA); (** A *)
  in(cA,xc);
  let kmacA = try find (j:index) such that xc = (encap_public (r(i,j)) epkA)
   in kdf(<tagmac,<epkA,xc>>, diff(kBh(i, j), decap xc (eskA i)))
   else kdf(<tagmac, <epkA,xc>>, decap xc (eskA i))
  in
  out(cA,rA(i)); (** A1 *)
  in(cA,x);
  let xB = fst(x) in
  let xrB = fst(snd(x)) in
  let xsigmaB = fst(snd(snd(x))) in
  let xmacB = snd(snd(snd(x))) in
  if xB = b &&
     checksign(<tag0,<<epkA,xc>,<rA(i),xrB>>>, xsigmaB,vk(skB)) &&
     mac(<tag0,b>,kmacA) = xmacB then
  out(cA, <a,<sign(<tag1,<<epkA,xc>,<rA(i),xrB>>>,skA), mac(<tag1,a>,kmacA)>>). (** A2 *)
  (** A3 : else branch *)


(** Note: in the final proof, to enrich with the sequence it is important 
that r is parametrized by i and j, and similarly for KBh *)
(** The idealisation is not done in the same way in both parts. 
This may cause some difficulties to put the two parts together *)

(** Ideal B which outputs kfresh if it receives pk(eskA) *)
process B_ideal_normal(j:index)=
  in(cB,yepkA);
  let c =
     try find (i:index) such that yepkA = kem_pub (eskA i)
     in encap_public (r(i,j)) yepkA
     else encap_public (r' j) yepkA
  in
  let kB =  
     try find (i:index) such that yepkA = kem_pub (eskA i)
     in diff((kBh(i,j)), encap_shared (r(i,j)) yepkA)
     else encap_shared (r' j) yepkA
  in
  out(cB,c);
  in(cB,yrA);
  let kmacB = kdf(<tagmac,<yepkA,c>>,kB) in
  let sigmaB = sign(<tag0,<<yepkA,c>,<yrA,rB(j)>>>,skB) in
  let macB = mac(<tag0,b>,kmacB) in
  out(cB,<b,<rB(j),<sigmaB,macB>>>);
  in(cA,y);
  let yA = fst(y) in
  let ysigmaA = fst(snd(y)) in
  let ymacA = snd(snd(y)) in
  if yA=a &&
     checksign(<tag1,<<yepkA,c>,<yrA,rB(j)>>>,ysigmaA,vk(skA)) &&
     mac(<tag1,a>,kmacB) = ymacA then
  let keyB = kdf(<tagke,<<yrA,rB(j)>,<a,b>>>, kB)
  in out(cB,keyB).


system [postquantum] idealnormal = (!_i A : A_ideal_normal(i) | !_j B : B_ideal_normal(j)).

(** ---------------------------------------------------------------------- *)


lemma [idealnormal/right,idealnormal/left] diff_eq ['a] (x:'a) : diff(x,x) = x.
Proof. by project. Qed.
axiom [any] gt_def (x,y:index) : x > y <=> y < x.


name kfresh : kem_shared.

(** ------- collisionKEM ---------------- *)

(** On the left *)

global lemma [idealnormal/left,idealnormal/left] GcollKEML (i,j1,j2:index[const], k:index):
  [encap_public (r(i,j1)) (kem_pub (eskA k)) =
   encap_public (r(i,j2)) (kem_pub (eskA k))
   =>
   j1 = j2].
Proof.
  nosimpl ghave Hij : [j1 = j2 || j1 <> j2] by auto.
  case Hij; 1: auto.
  intro H.
  ghave He : [j1 <> j2] ->
           equiv(kem_pub (eskA k),
                 diff(encap_shared (r(i,j2)) (kem_pub (eskA k)),kfresh),
                 encap_public (r(i,j1)) (kem_pub (eskA k)),
                 encap_public (r(i,j2)) (kem_pub (eskA k)),
                 encap_shared (r(i,j1)) (kem_pub (eskA k))).
  intro _; by crypto KEM_CPA_SINGLE. 

  assert (kfresh = encap_shared (r(i,j1)) (kem_pub (eskA k))).
  have G := He  Hij.
project => //.    

rewrite equiv -G => //.
by rewrite !-decap_encap H.

rewrite equiv -G => //.
by rewrite !-decap_encap H.

  fresh Meq.
Qed.




lemma [idealnormal/left] collisionKEML (i,j1,j2:index[const], k: index):
  encap_public (r(i,j1)) (kem_pub (eskA k)) =
   encap_public (r(i,j2)) (kem_pub (eskA k))
   =>
   j1 = j2.
Proof. 
use GcollKEML with i,j1,j2,k. auto. 
 Qed.



(** On the right *)

global lemma [idealnormal/right,idealnormal/right] GcollKEMR (i,j1,j2:index[const], k:index):
  [encap_public (r(i,j1)) (kem_pub (eskA k)) =
   encap_public (r(i,j2)) (kem_pub (eskA k))
   =>
   j1 = j2].
Proof.
  nosimpl ghave Hij : [j1 = j2 || j1 <> j2] by auto.
  case Hij; 1: auto.
  intro H.
  ghave He : [j1 <> j2] ->
           equiv(kem_pub (eskA k),
                 diff(encap_shared (r(i,j2)) (kem_pub (eskA k)),kfresh),
                 encap_public (r(i,j1)) (kem_pub (eskA k)),
                 encap_public (r(i,j2)) (kem_pub (eskA k)),
                 encap_shared (r(i,j1)) (kem_pub (eskA k))).
  intro _; by crypto KEM_CPA_SINGLE. 

  assert (kfresh = encap_shared (r(i,j1)) (kem_pub (eskA k))).
  have G := He  Hij.
project => //.    

rewrite equiv -G => //.
by rewrite !-decap_encap H.

rewrite equiv -G => //.
by rewrite !-decap_encap H.

  fresh Meq.
Qed.




lemma [idealnormal/right] collisionKEMR (i,j1,j2:index[const], k: index):
  encap_public (r(i,j1)) (kem_pub (eskA k)) =
   encap_public (r(i,j2)) (kem_pub (eskA k))
   =>
   j1 = j2.
Proof. 
use GcollKEMR with i,j1,j2,k. auto. 
 Qed.




lemma [any] eq_eq['a]: forall (x,y:'a), x = y => x=y.
Proof.
auto.
Qed.


axiom [any] pk_injectivity (i,j:index) : kem_pub(eskA(i)) = kem_pub(eskA(j)) <=> i = j.


lemma [any] tryFind0(i:index) :
  forall m:index -> index -> message, forall t:index -> message,
  try find (i0:index) such that (kem_pub(eskA(i)) = kem_pub(eskA(i0))) in (m i i0) else (t i)   
  = m i i.
Proof.
  rewrite pk_injectivity. intro m  t.
  case (try find (i0:index) such that i=i0 in m i i0 else t i).
  + intro  [ij [Hi Hm]]. auto.
  + intro [Hn _].
    by use Hn with i.
Qed.


lemma [any] tryFind0Shared(i:index) :
  forall m:index -> index -> kem_shared, forall t:index -> kem_shared,
  try find (i0:index) such that (kem_pub(eskA(i)) = kem_pub(eskA(i0))) in (m i i0) else (t i)   
  = m i i.
Proof.
  rewrite pk_injectivity. intro m  t.
  case (try find (i0:index) such that i=i0 in m i i0 else t i).
  + intro  [ij [Hi Hm]]. auto.
  + intro [Hn _].
    by use Hn with i.
Qed.


lemma [any] tryFind(i:index,j0:index) :
  try find (i0:index) such that (kem_pub(eskA(i)) = kem_pub(eskA(i0))) 
           in (encap_public (r(i0,j0)) (kem_pub (eskA i))) 
           else encap_public (r' j0) (kem_pub (eskA i)) 
  = encap_public (r(i,j0)) (kem_pub (eskA i)).
Proof.
  by use tryFind0 with i,(fun (i:index) => fun (i0:index) => encap_public (r(i0,j0)) (kem_pub (eskA i))),(fun (i:index) => encap_public (r' j0) (kem_pub (eskA i))).
Qed.

lemma [any] tryFindShared(i:index,j0:index,j:index) :
try find (i0:index) such that (kem_pub (eskA i) =kem_pub (eskA i0)) in (kBh(i0, j)) else encap_shared (r' j) (kem_pub (eskA i)) = kBh(i,j).
Proof.
  by use tryFind0Shared with i,(fun (i:index) => fun (i0:index) => (kBh(i0,j))),(fun (i:index) => encap_shared  (r' j) (kem_pub (eskA i))). 
Qed.

lemma [any] tryFindShared2(i:index,j0:index,j:index) :
try find (i0:index) such that (kem_pub (eskA i) =kem_pub (eskA i0)) in (encap_shared (r(i0, j)) (kem_pub (eskA i))) else encap_shared (r' j) (kem_pub (eskA i)) = encap_shared (r(i, j)) (kem_pub (eskA i)).
Proof.
  by use tryFind0Shared with i,(fun (i:index) => fun (i0:index) => (encap_shared (r (i0,j)) (kem_pub (eskA i)))),(fun (i:index) => encap_shared  (r' j) (kem_pub (eskA i))). 
Qed.


lemma [idealnormal] KMacAgreement :
  forall i:index, forall j:index,
  happens(A1(i)) && happens(B1(j)) &&
  input@B(j) = kem_pub (eskA i) && output@B(j) = input@A1(i) =>  kmacB(j)@B1(j) = kmacA(i)@A1(i).

Proof.
  intro i j [HapA HapB HinputBj HoutputBj].
  rewrite /kmacA /kmacB /epkA /c HinputBj. rewrite tryFind. rewrite -HoutputBj.
  assert(happens(B(j))) by depends B(j),B1(j).
  rewrite /output /c HinputBj tryFind.
  case (try find (j0:index) such that _ in kdf(_,_) else _).
  ++ intro [j0 [Henc Hsimple]]. case (j=j0). simpl.  
     rewrite Hsimple.  rewrite /kB. 
     rewrite HinputBj. 
     intro Eq. rewrite -HoutputBj. 
     rewrite /output. rewrite /c. rewrite HinputBj.  rewrite tryFind. project.

use tryFindShared with i, j0, j.
rewrite Meq.
rewrite Eq => //.  rewrite decap_encap.
case(try find i0:index such that (kem_pub (eskA i) = kem_pub (eskA i0))
   in encap_shared (r(i0, j)) (kem_pub (eskA i))
   else encap_shared (r' j) (kem_pub (eskA i))).
+ intro [i0 [H1 H2]]. rewrite H2. use pk_injectivity with i, i0 => //. destruct H as [Ha Hb]. assert(i0=i) => //.
+ intro [H1 H2]. use H1 with i. auto. auto.

     intro Neq. project. 
     use collisionKEML with i, j, j0, i. auto.
     use collisionKEMR with i, j, j0, i. auto. 
  ++ intro [Henc Hsimple]. by use Henc with j.
Qed.


lemma [idealnormal] WauthA_iff :
  forall (tau:timestamp), forall (i:index),
  happens(tau) && (tau = A2(i) || tau = A3(i)) =>
  (xB(i)@tau = b &&
   checksign (<tag0,<<epkA(i)@A(i),input@A1(i)>,<rA(i),xrB(i)@tau>>>, xsigmaB(i)@tau,vk (skB)) &&
   mac (<tag0,b>, kmacA(i)@A1(i)) = xmacB(i)@tau)
  <=>
  exists j:index, (B1(j) < tau
    && fst(output@B1(j)) = fst(input@tau)
    && fst(snd(output@B1(j))) = fst(snd(input@tau))
    && fst(snd(snd(output@B1(j)))) = fst(snd(snd(input@tau)))
    && snd(snd(snd(output@B1(j)))) = snd(snd(snd(input@tau)))
    && A1(i) < tau   && output@A1(i) = input@B1(j)
    && B(j)  < B1(j) && output@B(j)  = input@A1(i)
    && A(i)  < A1(i) && output@A(i) = input@B(j)).
Proof.
  intro tau. intro i [Hap HapA].
  assert(A1(i) < tau) by (destruct HapA as [_|_]; by depends A1(i),tau).
  use depends_A_A1 with i; [2: constraints].

  assert(epkA(i)@tau = kem_pub(eskA i)) as Exp_epkA by destruct HapA as [_|_]; rewrite /epkA.

  split.
  * (** => *)
    intro HcondA. destruct HcondA as [EqA EqSignA EqMacA].

    euf EqSignA. intro [j0 [HA1 HA2]].
    assert (B1(j0) < tau) by (destruct HA1 as [HA1A| HA1B]; by destruct HapA as [HapA2 | HapA3]).
    clear HA1. rewrite /c in HA2.

    assert(input@B(j0) = kem_pub(eskA(i))) as HinputB by destruct HapA as [_|_].
    rewrite HinputB tryFind in HA2.
    use depends_B_B1 with j0; [2:constraints].
    exists j0. rewrite /output. repeat split.
+  constraints. 
    + by destruct HapA as [HapA1 | HapA2]. 
    + by destruct HapA as [HapA1 | HapA2].
    + rewrite /sigmaB.
      use sufcma with
        <tag0,<<epkA(i)@tau,input@A1(i)>,<rA(i),xrB(i)@tau>>>,xsigmaB(i)@tau,skB as EqCMA; [2: 
         rewrite Exp_epkA; rewrite /epkA in EqSignA; assumption].
      rewrite /c HinputB tryFind. by destruct HapA as [_ | _].
    + rewrite /macB.
      assert(input@A1(i) = encap_public (r (i,j0)) (kem_pub (eskA i))) as HinputA1 by auto.
      assert( kmacA(i)@A1(i) = kdf(<tagmac,<kem_pub (eskA i),input@A1(i)>>, diff(kBh(i, j0), decap (input@A1(i)) (eskA i)) )) as HkA. {
        rewrite /kmacA HinputA1 /epkA.
        assert forall j:index,
          encap_public (r (i,j0)) (kem_pub (eskA i)) =
          encap_public (r (i,j))  (kem_pub (eskA i))
          <=> j = j0. intro j.  split. project.
            use collisionKEML with i, j, j0, i. auto. 
            use collisionKEMR with i, j, j0, i. auto. 
        intro *. rewrite Ieq. constraints.  rewrite H.
        case (try find (j:index) such that j = j0 in kdf(_,_) else _).
        - intro *. rewrite !HinputA1. destruct H0 as [j [H0a H0b]]. rewrite HinputA1 in H0b. rewrite H0b. congruence. 
        - intro [Hn _]; by use Hn with j0.
      }.
      destruct HapA as [HapA1 | HapA2].

       rewrite /kmacB /c HinputB tryFind -HinputA1. simpl. rewrite HapA1 in EqMacA. rewrite /kB. rewrite !HinputA1 in HkA. simpl. rewrite !HinputB.
rewrite HinputA1. rewrite  /xmacB in EqMacA. project. use tryFindShared with i, j0, j0. rewrite Meq. simpl. constraints. 
use tryFindShared2 with i, j0,j0.
rewrite Meq.
auto. 
  rewrite /kmacB /c HinputB tryFind -HinputA1. simpl. rewrite HapA2 in EqMacA. rewrite /kB. rewrite !HinputA1 in HkA. simpl. rewrite !HinputB.
rewrite HinputA1. rewrite  /xmacB in EqMacA. project. 
  use tryFindShared with i, j0,j0.
rewrite Meq. auto. 
 use tryFindShared2 with i, j0,j0.
rewrite Meq. auto. 
+ constraints.
+ congruence.
+ constraints.    
+ by rewrite /c HinputB tryFind.
+ constraints. 
+ congruence.

  * (** Second implication *)
    intro [j [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11]].
    use KMacAgreement with i,j as KMacAgreement1.
    rewrite -KMacAgreement1.
    by destruct HapA as [HapA2 | HapA3].
    repeat split. constraints. constraints. rewrite -H11 /output /epkA; constraints. 
      congruence.  
Qed.


lemma [idealnormal] WauthA_eq :
  forall (tau:timestamp), forall (i:index),
  happens(tau) && (tau = A2(i) || tau = A3(i)) =>
  (xB(i)@tau = b &&
    checksign (<tag0,<<epkA(i)@A(i),input@A1(i)>,<rA(i),xrB(i)@tau>>>, xsigmaB(i)@tau,vk (skB)) &&
         mac (<tag0,b>, kmacA(i)@A1(i)) = xmacB(i)@tau)
  =
  exists (j:index),
    (B1(j) < tau
     && fst(output@B1(j)) = fst(input@tau)
     && fst(snd(output@B1(j))) = fst(snd(input@tau))
     && fst(snd(snd(output@B1(j)))) = fst(snd(snd(input@tau)))
     && snd(snd(snd(output@B1(j)))) = snd(snd(snd(input@tau)))
     && A1(i) < tau   && output@A1(i) = input@B1(j)
     && B(j)  < B1(j) && output@B(j)  = input@A1(i)
     && A(i)  < A1(i) && output@A(i) = input@B(j)).
Proof.
  intro tau i.
  intro H. rewrite eq_iff.
  use WauthA_iff with tau,i.
  by apply H0. constraints.
Qed.


lemma [idealnormal] axA2_input_A1_A2 : forall (i:index),
  happens(A2(i)) => cond@A2(i) => (exists j0:index,
  (forall t:message, forall m:index -> message,
   try find j such that input@A1(i) = encap_public (r (i,j)) (kem_pub (eskA i))
              in m j
              else t
   = m j0)
 && (input@A1(i) = encap_public (r(i,j0)) (kem_pub (eskA i)))).
Proof.
  intro i. intro Ha Hc.
  use WauthA_iff with A2(i),i; 2: constraints. destruct H as [W1 W2]. clear W2.
  expand cond@A2(i).
  use W1 with Hc. destruct H as [j [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11]].
  expand output@B(j). expand c(j)@B(j). expand output@A(i). expand epkA(i)@A(i).
  rewrite -H11 in H9. simpl.
  use tryFind with i as Htf0.
  use Htf0 with j as Htf.
  rewrite Htf in H9. clear Htf. exists j. split.
  intro t. rewrite -H9. intro m.
  case (try find (j0:index) such that _ in m j0 else t).
  ++ intro [j0 [Heq Htf]]. rewrite Htf. case(j=j0).  intro H;  congruence.   intro Neq. project.
   use collisionKEML with i, j, j0,  i. constraints. 
   use collisionKEMR with i, j, j0,  i. constraints.
  ++ intro [Habsurd _]. by use Habsurd with j. congruence. 
 Qed.


lemma [idealnormal] WauthB_iff :
  forall tau:timestamp, forall (j:index),
  (happens(tau) && (tau = B2(j) || tau = B3(j)) && exec@pred(tau)) =>
  (exec@pred(tau) && happens(tau) &&
   yA(j)@tau = a &&
   checksign (<tag1,<<input@B(j),c(j)@B(j)>,<input@B1(j),rB j>>>,
              ysigmaA(j)@tau, vk (skA)) &&
   mac (<tag1,a>, kmacB(j)@B1(j)) = ymacA(j)@tau )
  <=>
  exists (i:index),
    (exec@pred(tau)
     && A2(i) < tau
     && fst(output@A2(i)) = fst(input@tau)
     && fst(snd(output@A2(i))) = fst(snd(input@tau))
     && snd(snd(output@A2(i))) = snd(snd(input@tau))
     && B1(j) < tau
     && fst(output@B1(j)) = fst(input@A2(i))
     && fst(snd(output@B1(j))) = fst(snd(input@A2(i)))
     && fst(snd(snd(output@B1(j)))) = fst(snd(snd(input@A2(i))))
     && snd(snd(snd(output@B1(j)))) = snd(snd(snd(input@A2(i))))
     && A1(i) < A2(i) && output@A1(i) = input@B1(j)
     && B(j) < B1(j)  && output@B(j)  = input@A1(i)
     && A(i) < A1(i) && output@A(i) = input@B(j)).
Proof.
  intro tauB j.
  intro [Hap HtauB Hexec].
  (** Lemmas used to avoid case split in further proof *)

  (** dependency *)
  assert(B1(j) < tauB) by destruct HtauB as [HtauB2 | HtauB3]; depends B1(j), tauB.


  (** expansions *)
  assert(c(j)@B(j) =
     try find i:index such that (input@B(j) = kem_pub (eskA i))
      in encap_public (r (i,j)) (input@B(j))
      else encap_public (r' j) (input@B(j))) as  Exp_c
  by destruct HtauB as [HB2 | HB3]; try expand c(j)@tauB.

  assert( ysigmaA(j)@tauB = fst(snd(input@tauB)) ) as Exp_ysigmaA
  by destruct HtauB as [HtauB2 | HtauB3]; try expand ysigmaA(j)@tauB.

  assert(ymacA(j)@tauB = snd (snd (input@tauB))) as Exp_ymacA
  by destruct HtauB as [_|_]; try expand ymacA(j)@tauB.

  assert(yA(j)@tauB = fst(input@tauB)) as Exp_yA
  by destruct HtauB as [_|_]; try expand yA(j)@tauB.

  split.

  * (** => *)
    rewrite Hexec Hap; simpl.
    intro Hcond. destruct Hcond as [EqB EqSignB EqMacB].

    rewrite Exp_ysigmaA in *.

    euf EqSignB.
    intro [i [H1 H2]]. exists i.

    assert (A2(i) < tauB). {
      destruct H1 as [H11| H12|H13]; [1,3: constraints | 2: use depends_B_B1 with j; constraints; constraints].
    }.

    use executability with pred(tauB) as executable; [2: constraints | 3: assumption].
    use executable with A2(i); [2: constraints].  clear executable.
    expand exec@A2(i).
    destruct H as [HexecpA2  HcondA2].
    use WauthA_iff with A2(i),i; [2: constraints ].
    destruct H as [HL HR].
    expand cond@A2(i).
    use HL with HcondA2.

    destruct H as [j0 [Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 Ha8 Ha9 Ha10 Ha11]].
    clear HL HR.
    assert j0 = j as Heq. clear EqSignB EqMacB Exp_c Exp_ymacA Exp_ysigmaA. auto.
    rewrite Heq in *; clear Heq.
   
    assert input@B(j) = kem_pub (eskA i). { rewrite -Ha11 /output /epkA. constraints. }
    rewrite Meq in H2.
    simpl. 

    use KMacAgreement with i,j;    [2: repeat split; constraints; constraints; assumption; assumption].


    split.
     expand output@A2(i). 

     use sufcma with  <tag1,<<input@B(j),c(j)@B(j)>,<input@B1(j),rB(j)>>>, fst (snd (input@tauB)), skA. simpl. constraints.  assumption. 

rewrite /output. simpl. rewrite /epkA.  rewrite -Meq.  rewrite -Ha9. rewrite /output.

     use sufcma with  <tag1,<<input@B(j),c(j)@B(j)>,<input@B1(j),rB(j)>>>, fst (snd (input@tauB)), skA.  rewrite -Ha7 /output in Meq1. rewrite /xrB -Ha3 /output. simpl. assumption. assumption. 

  * (** <= *)
intro [i [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16]].
  assert(cond@tauB = ((yA(j)@tauB = a && checksign(<tag1,<<input@B(j),c(j)@B(j)>,<input@B1(j),rB j>>>,
           ysigmaA(j)@tauB, vk (skA)) &&  mac (<tag1,a>, kmacB(j)@B1(j)) = ymacA(j)@tauB) = (tauB = B2(j)))) as Exp_cond.
  { rewrite eq_iff. split.
    + intro Hrw. destruct HtauB as [HB | HB]. rewrite /cond in Hrw; rewrite Hrw HB eq_iff; clear Hrw. simpl. constraints.    
 rewrite /cond in Hrw; rewrite Hrw HB eq_iff; clear Hrw.    simpl. constraints. 
    + intro Hrw. destruct HtauB as [HB | HB].  rewrite /cond Hrw. constraints. rewrite /cond Hrw. constraints.
  }.

  clear Hexec. rewrite H1. rewrite Hap. simpl.

 rewrite Exp_ysigmaA.

  use depends_B_B1 with j; [2:constraints]. 
  use depends_A_A1 with i; [2: constraints].


repeat split.  
        + auto.
        + destruct HtauB as [HtauB2 | HtauB3].  
              ++ rewrite HtauB2 in *.  simpl. expand cond@B2(j). expand ysigmaA(j)@B2(j). expand output@A2(i). simpl.   rewrite -H4.  expandall.  simpl. rewrite H14.  auto. 
              ++ rewrite HtauB3 in *.  simpl. expand cond@B3(j). expand ysigmaA(j)@B3(j). expand output@A2(i).  rewrite -H4. simpl.  rewrite /xrB. rewrite -H16 /output /c /epkA -H12 -H14 /output /c. 
auto. 
        + destruct HtauB as [HtauB2 | HtauB3].
                ++ rewrite HtauB2 in *.  simpl. expand ymacA(j)@B2(j). rewrite -H5. rewrite /output. simpl. 
                   use KMacAgreement with i,j.  clear Exp_cond H1 H10 H12 H14 H16 H3 H4 H5 H7 H8 H9.
                
 expandall. simpl. constraints. 
 repeat split. constraints. constraints. rewrite -H16 /output /epkA; constraints; constraints. constraints.
               ++ rewrite HtauB3 in *.  simpl. expand ymacA(j)@B3(j). rewrite -H5. rewrite /output. simpl. 
                   use KMacAgreement with i,j.  clear Exp_cond H1 H10 H12 H14 H16 H3 H4 H5 H7 H8 H9.
 expandall. simpl. constraints. 
 repeat split. constraints. constraints. rewrite -H16 /output /epkA; constraints; constraints. constraints.

Qed.




lemma [idealnormal] WauthB_eq :
  forall tau:timestamp, forall (j:index),
  (happens(tau) && (tau = B2(j) || tau = B3(j)) && exec@pred(tau)) =>
  (yA(j)@tau = a &&
    checksign (<tag1,<<input@B(j),c(j)@B(j)>,<input@B1(j),rB j>>>,
           ysigmaA(j)@tau, vk (skA)) &&
    mac (<tag1,a>, kmacB(j)@B1(j)) = ymacA(j)@tau)
  =
  exists (i:index),
    (exec@pred(tau)
     && A2(i) < tau
     && fst(output@A2(i)) = fst(input@tau)
     && fst(snd(output@A2(i))) = fst(snd(input@tau))
     && snd(snd(output@A2(i))) = snd(snd(input@tau))
     && B1(j) < tau
     && fst(output@B1(j)) = fst(input@A2(i))
     && fst(snd(output@B1(j))) = fst(snd(input@A2(i)))
     && fst(snd(snd(output@B1(j)))) = fst(snd(snd(input@A2(i))))
     && snd(snd(snd(output@B1(j)))) = snd(snd(snd(input@A2(i))))
     && A1(i) < A2(i) && output@A1(i) = input@B1(j)
     && B(j)  < B1(j) && output@B(j)  = input@A1(i)
     && A(i)  < A1(i) && output@A(i) = input@B(j)).
Proof.
  rewrite eq_iff. intro tau j. intro [HapTau Htau Hexec].  use WauthB_iff with tau,j as WA.
  by rewrite HapTau Hexec in *. by auto.
Qed.

lemma [idealnormal] axB2_input_B : forall (j:index),
  happens(B2(j)) =>  exec@B2(j) => exists i:index,
  (forall t:message, forall m:index -> message,
   try find i0 such that input@B(j) = kem_pub (eskA i0)  in m i0 else t = m i)
  && (input@B(j) = kem_pub (eskA i))
  && (input@B1(j) = rA(i)).
Proof.
  intro j HapB2 Hexec. use WauthB_eq with B2(j),j as WA. simpl.
  expand exec@B2(j). expand cond@B2(j).
  destruct Hexec as [Hexec Hcond]. rewrite Hcond in WA. simpl.
  destruct WA as [i [WA1 WA2 WA3 WA4 WA5 WA6 WA7 WA8 WA9 WA10 WA11 WA12 WA13 WA14 WA15 WA16]].
  exists i. rewrite -WA16. rewrite /output /epkA.
  assert forall (t:message,m:index -> message),
   try find i0:index such that (kem_pub (eskA i) = kem_pub (eskA i0))
   in m i0 else t = m i as GenConc.
  {
   intro t. intro m. case (try find (i0:index) such that (kem_pub(_) = _) in m i0 else t).
   ++ intro [i0 [Heq Htf]]. rewrite Htf. assert(i = i0).
      {use pk_injectivity with i,i0 as pk_inj. rewrite Heq in pk_inj. simpl. by rewrite -eq_iff in pk_inj. }.
  rewrite Ieq. constraints.
   ++ intro [Habsurd _]. by use Habsurd with i.
  }.
  by rewrite GenConc.
  repeat split. constraints. constraints. rewrite /exec in Hexec. constraints. 
Qed.



lemma [idealnormal] ITF_A1 (i:index) :
  try find j such that input@A1(i) = encap_public (r (i,j)) (kem_pub (eskA i)) in
    encap_public (r (i,j)) (kem_pub (eskA i)) else input@A1(i)
    =
    input@A1(i).
Proof.
  by case (try find (j:index) such that _ in _ else input@A1(i)).
Qed.


abstract max_index : index.
axiom [any] max_index (i:index) : i <= max_index.
global axiom [any] index_split (i : index[const]) :
  [forall j, j <= i <=> j = i] \/
  Exists (j:index[const]), [forall k, k < i <=> k <= j].

let aux =
    (skA,skB,
     seq(i:index => kem_pub (eskA i)),
     seq(j:index => r'(j)),
     seq(i:index => rA(i)),
     seq(j:index => rB(j))).

(** KEM_CPA step using crypto tactic = basic step in hybrid argument *)
global lemma [idealnormal/right,idealnormal/right] crypto_application (N:index[const]) : equiv(
 aux,
 (** diff(real,ideal) encap for key N *)
 fun (i:index) =>
   if (i = N) then
     (fun j =>
        (encap_public (r (i, j)) (kem_pub (eskA i)),
         diff(encap_shared (r (i, j)) (kem_pub (eskA i)),
              kBh (i, j))))
   else (fun _ => (empty, empty_shared)),
 (** real encap for newer keys and ideal encap for older ones *)
 fun (i:index) =>
   if (i < N) then
     (fun j =>
        (encap_public (r (i, j)) (kem_pub (eskA i)),
         kBh (i, j)))
   else (fun _ => (empty, empty_shared)),
 fun (i:index) =>
   if (i > N) then
     (fun j =>
        (encap_public (r (i, j)) (kem_pub (eskA i)),
         encap_shared (r (i, j)) (kem_pub (eskA i))))
   else (fun _ => (empty, empty_shared))
).
Proof.
  by crypto KEM_CPA (skey : eskA N).
Qed.
(** Note that the system is actually irrelevant here. However it is important to use
   directly the one we'll need in the end, because changing it using transitivity later on
   can be painful. *)
global lemma [idealnormal/right,idealnormal/left] base_case (N:index[const]) :
  equiv(
   (** auxiliary material *)
   aux,
   (** diff(real,ideal) encap for keys up to N *)
   (fun i =>
      if i <= N then
        fun j =>
          (encap_public (r (i, j)) (kem_pub (eskA i)),
           diff(encap_shared (r (i, j)) (kem_pub (eskA i)), kBh (i, j)))
      else fun _ => (empty,empty_shared)),
   (** real encap for newer keys *)
   (fun i =>
      if i > N then
        fun j =>
          (encap_public (r (i, j)) (kem_pub (eskA i)),
           encap_shared (r (i, j)) (kem_pub (eskA i)))
      else fun _ => (empty,empty_shared))).
Proof.
  trans [idealnormal/right,idealnormal/right]; 1,3: rewrite /aux; refl.
  induction N => N IH.
  have [HN|[P HN]] := index_split N.
  + rewrite HN in 1.
    by crypto KEM_CPA (skey : eskA N).
  + splitseq 1: (fun i => i = N) (fun _ => (empty,empty_shared)).
    enrich (fun i => if i = N then
              (fun (j:index) =>
                 (encap_public (r (i, j)) (kem_pub (eskA i)),
                  diff(encap_shared (r (i, j)) (kem_pub (eskA i)), kBh (i, j))))
            else (fun _ => (empty, empty_shared))).
    deduce 2.
    rewrite /= if_then_then -lt_charac in 2.
    (** We have at 2: j<N; at 0: j=N; at 3: j>N.
       The equivalence
         real<N | real=N | real>N ~ ideal<N | ideal=N | real>N
       follows from
         real<N | real=N | real>N ~ ideal<N | real=N | real>N  by IH P
       and
         ideal<N | real=N | real>N ~ ideal<N | ideal=N | real>N by crypto_application.
       We use trans by specifying elements 3 and 2 in the middle sequence. *)
    trans
      2: fun (i:index) =>
           if (i < N) then
             (fun j =>
                (encap_public (r (i,j)) (kem_pub (eskA i)),
                 kBh (i, j)))
           else (fun _ => (empty, empty_shared)),
      0: fun (i:index) =>
           if (i = N) then
             (fun j =>
                (encap_public (r (i,j)) (kem_pub (eskA i)),
                 encap_shared (r (i,j)) (kem_pub (eskA i))))
           else (fun _ => (empty, empty_shared)).
    - (** work on conditions before applying IH P *)
      rewrite !HN in 2.
      enrich fun (i:index) =>
        if (i > P) then
          (fun j =>
            (encap_public (r (i, j)) (kem_pub (eskA i)),
             encap_shared (r (i, j)) (kem_pub (eskA i))))
        else (fun _ => (empty, empty_shared)).
       (** 1 and 4 are now subsumed by 0; IMPROVE reasoning e.g. by avoiding gt (>) *)
       assert forall j, j > N <=> j > N && j > P as H1. {. 
         intro j. rewrite (gt_def j N) (gt_def j P). split; 2: auto. intro H. split; 1: auto.
         assert P < N by rewrite HN. by apply (lt_trans P N j).
       }.
       rewrite H1 in 4. deduce 4.
       assert forall j, j = N <=> j = N && j > P as H2. {. 
         intro j. rewrite (gt_def j P). split; 2: auto. intro H. split; 1: auto.
         assert P < N by rewrite HN. auto.
       }.
       rewrite (diff_eq
         (fun (i:index) =>
           if (i = N) then
            (fun j =>
               (encap_public (r (i, j)) (kem_pub (eskA i)),
                encap_shared (r (i, j)) (kem_pub (eskA i))))
           else (fun _ => (empty, empty_shared)))) in 1.
       rewrite H2 -if_then_then /= in 1. deduce 1.
       apply (IH P).
       by rewrite HN.
    - apply crypto_application N.
Qed.

global theorem [idealnormal] equivIdealNormal (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(
    (skA,skB,
     (fun i => kem_pub (eskA i)),
     (fun i j => (encap_public (r (i,j)) (kem_pub (eskA i)),
                  diff((kBh (i,j)), encap_shared (r (i,j)) (kem_pub (eskA i))))),
     (fun j => r'(j)),
     (fun i => rA(i)),
     (fun j => rB(j))),
    frame@tau).
Proof.
  intro Hap.
  induction tau.

  + (** init *)
    expandall.
    sym.
    have H := base_case max_index.
    rewrite /aux if_true in H. intro *; apply max_index.
    apply H.

  + (** A *)
    rewrite /frame /state /transcript /output /epkA; fa (_,_,_), !<_,_>; simpl. 
    rewrite /input. fa 2. fa (qatt _). { constraints.  }
    apply IH.

  + (** A1 *)
    rewrite /frame /state /transcript /output; fa (_,_,_), !<_,_>; simpl.
    rewrite /input. fa 2. fa(qatt _). { constraints.  }
    apply IH.

  + (** A2 *)
    rewrite /frame /state /transcript; fa (_,_,_), !<_,_>. 
    assert
      if exec@A2(i) then output@A2(i)
      =
      if exec@A2(i)  then
        try find j such that
          (input@A1(i) = encap_public (r (i,j)) (epkA(i)@A2(i)))
        in
          <a,
           <sign (<tag1,
                   <<epkA(i)@A2(i),input@A1(i)>,<rA i,fst (snd (input@A2(i)))>>>,
                  skA),
            mac(<tag1,a>,
                kdf(<tagmac,<epkA(i)@A2(i), encap_public (r (i,j)) (epkA(i)@A2(i))>>,
                diff((kBh (i,j)), encap_shared (r (i,j)) (epkA(i)@A2(i)))))>>
      as aux_A2_output.
    { rewrite /output. expand exec@A2(i).
      case cond@A2(i); 2:auto. intro Hcond. simpl. 
      use axA2_input_A1_A2 with i as [j0  [ax3 ax4]] => //.
      rewrite !ax3.  rewrite -ITF_A1. rewrite !ax3. rewrite /xrB /epkA. rewrite !ax4. auto. }. 

 rewrite aux_A2_output.   clear aux_A2_output.
    fa (if _ then _). expand epkA(i)@A2(i). fa 0.
    deduce 12. (** try find *)
    rewrite /exec /cond WauthA_eq in 11; 1: auto.  deduce 11.

    rewrite /input. fa 8. fa(qatt _). {  constraints.  }
    by apply IH.

  (** A3 ok *)
  (** 1/ prove a lemma WauthA *)
  (** 2/ get rid of cond@A3 *)
  + rewrite /frame /state /transcript; fa (_,_,_), !<_,_>.
    expand exec@A3(i). expand output@A3(i).
    expand cond@A3(i).
    rewrite WauthA_eq in 5; 1: constraints. 
    deduce 5.
    rewrite /input. fa 2. fa(qatt _). {constraints. }
    by apply IH.

  (** B ok *)
  + rewrite /frame /state /transcript /exec /cond /output /c. fa 0; fa (_,_,_), !<_,_>. simpl.
    (** Working on if exec then _ *)
    assert
      forall i:index,
      input@B(j) = kem_pub (eskA i) =>
      encap_public (r (i,j)) (input@B(j)) =
      encap_public (r (i,j)) ( kem_pub (eskA i)) as Hrw. { intro *. rewrite Meq. constraints. }
     assert(if exec@pred (B(j)) then
     try find i:index such that (input@B(j) = kem_pub (eskA i))
     in encap_public (r (i,j)) (input@B(j))
     else encap_public (r' j) (input@B(j))  
     = 
     if exec@pred (B(j)) then
     try find i:index such that (input@B(j) = kem_pub (eskA i))
     in encap_public (r (i,j)) (kem_pub (eskA i))
     else encap_public (r' j) (input@B(j))). rewrite Hrw => //. 
    rewrite H.
    fa (if exec@_ then _ ).

    rewrite /input. fa 8.
    fa 11. fa 11. fa 12.
    fa (qatt _). {constraints. }
    by apply IH.

  + (** B1 ok *)
    rewrite /frame /state /transcript /output /exec /cond; fa (_,_,_), !<_,_>; simpl.
    expand sigmaB(j)@B1(j). expand macB(j)@B1(j). (*expand c(j)@B1(j).*)
    expand kmacB(j)@B1(j).  (** expand c(j)@B1(j). *)
    fa 6. fa !<_,_>. fa sign _. fa mac _. fa kdf _. fa !<_,_>.
    assert
      (forall i,
       input@B(j) = kem_pub (eskA i) =>
       encap_public  (r (i,j)) (input@B(j)) =
       encap_public  (r (i,j)) (kem_pub (eskA i)))
      as Hrw by auto.
   assert( try find i:index such that (input@B(j) = kem_pub (eskA i))
   in encap_public (r (i,j)) (input@B(j))
   else encap_public (r' j) (input@B(j)) 
   = 
   try find i:index such that (input@B(j) = kem_pub (eskA i))
   in encap_public (r (i,j)) (kem_pub (eskA i))
   else encap_public (r' j) (input@B(j))). 
   rewrite Hrw => //.  
   rewrite H.
   rewrite /kB.
   assert( try find i:index such that (input@B(j) = kem_pub (eskA i))
   in diff(kBh (i,j), encap_shared (r (i,j)) (input@B(j)))
   else encap_shared (r' j) (input@B(j))
    =
   try find i:index such that (input@B(j) = kem_pub (eskA i))
   in diff(kBh (i,j), encap_shared (r (i,j)) (kem_pub (eskA i)))
   else encap_shared (r' j) (input@B(j))). 
   assert
      (forall i,
       input@B(j) = kem_pub (eskA i) =>
       encap_shared (r (i,j))  (input@B(j)) =
       encap_shared  (r (i,j)) (kem_pub (eskA i)))
      as Hrw2 by auto.
   rewrite Hrw2 => //.
   rewrite H0. 

   deduce 10. deduce 8. 
   expand input@B1(j). fa 2. 
   have Ord := depends_B_B1 j.
   fa(qatt _). {split; constraints. }
   apply IH.

  + (** B2 *)
    rewrite /frame /state /transcript; fa (_,_,_), !<_,_>.
    expand output@B2(j). expand keyB(j)@B2(j). expand kB(j)@B(j).
    assert
      (forall i,
       input@B(j) = kem_pub (eskA i) =>
       encap_public  (r (i,j)) (input@B(j)) =
       encap_public  (r (i,j)) (kem_pub (eskA i)))
      as Hrw by auto.

      assert
      (forall i,
       input@B(j) = kem_pub (eskA i) =>
       encap_shared (r (i,j))  (input@B(j)) =
       encap_shared  (r (i,j)) (kem_pub (eskA i)))
      as Hrw2 by auto.
    (** output *)
    assert
      (if exec@B2(j) then output@B2(j) =
       if exec@B2(j) then
      kdf
       (<tagke,<<input@B1(j),rB j>,<a,b>>>,
        try find i:index such that (input@B(j) = kem_pub (eskA i))
        in diff(kBh (i, j), encap_shared (r (i,j)) (kem_pub (eskA i)))
        else encap_shared (r' j) (input@B(j))))      as aux_B2_output.
     { rewrite /output.
      case exec@B2(j); 2: auto. intro Hexec. simpl.
      use axB2_input_B with j as [j0 [ax1 ax2 ax3]]; 2,3: auto.
      rewrite !ax3. expand keyB(j)@B2(j).
      expand kB(j)@B(j). rewrite ax3. 
      case (try find i such that (input@B(j) = kem_pub (eskA i))
            in diff(kBh (i,j), encap_shared (r (i,j)) (input@B(j))) else _).
      intro [i [Hm HH]]. rewrite HH.    
   rewrite Hrw2 => //.


rewrite Hrw2 in HH => //.    

intro [H1 H2]. rewrite ax2 in H1. 
use H1 with j0 => //. }
   rewrite Hrw2 => //.
    fa (if _ then _).
    clear aux_B2_output.
    (** exec *)
    rewrite /exec /cond.
    rewrite WauthB_eq in 5; 1: auto.
    deduce 5. 
    deduce 5. 
    rewrite /input. fa 2.  fa(qatt _). {constraints. }
    by apply IH.

 + (** B3 *)
   rewrite /frame /state /transcript /output.  fa (_,_,_), !<_,_>; simpl.
   (** getting rid of exec@B3(j) *)
   rewrite /exec /cond.
   rewrite WauthB_eq in 5; 1: auto.
   deduce 5. 
   rewrite /input. fa 2. fa(qatt _). {constraints. } 
   by apply IH.
Qed.
