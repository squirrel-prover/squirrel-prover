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


(** ---------------------------------------------------------------------- *)


signature sign, checksign, vk.
hash kdf where k:kem_shared.
hash mac.


axiom [any] sufcma :
  forall (m,s,sk:message), checksign(m,s,vk(sk)) => s = sign(m,sk).

abstract a : message.
abstract b : message.

abstract tag1   : message.
abstract tag0   : message.
abstract tagke  : message.
abstract tagmac : message.

axiom [any] tags_neq         : tag0  <> tag1.
axiom [any] tagke_tagmac_neq : tagke <> tagmac.

(** Long-term keys *)
name skA : message.
name skB : message.
 

(** Session keys for B. *)
name r      : index -> kem_randomness.
name r'     : index -> kem_randomness.
name rB     : index -> message.
name kS: index -> message.

name kBh: index -> kem_shared.

channel cA.
channel cB.

(** ---------------------------------------------------------------------- *)

(** Ideal A which runs with kB if it receives kfresh *)
(** Computation of KeyA has been removed *)

(** session keys for A *)
name eskA : index -> kem_skey.
name rA : index -> message.
process A_ideal(i:index) =
  let epkA = kem_pub (eskA i) in
  out(cA, epkA); (** A *)
  in(cA,xc);
  (** We now use kBh instead of the shared *)
  let kmacA = 
     try find (j:index) such that xc = encap_public (r j) epkA 
     in   kdf(<tagmac,<epkA,xc>>, kBh(j)) 
     else kdf(<tagmac,<epkA,xc>>,decap xc (eskA i)) 
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


(** Ideal B which outputs kfresh if it receives pk(eskA) *)
process B_ideal(j:index)=
  in(cB,yepkA);
  let c =
     try find (i:index) such that yepkA = kem_pub (eskA i) 
     in encap_public (r j) yepkA 
     else encap_public (r' j) yepkA 
  in
  out(cB,c);
  in(cB,yrA);
  let kmacB = 
  try find (i:index) such that yepkA = kem_pub (eskA i) 
     in kdf(<tagmac,<yepkA,c>>,kBh(j))
     else kdf(<tagmac,<yepkA,c>>, (encap_shared (r' j)  yepkA))
  in  
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
  let keyB = 
  try find (i:index) such that yepkA = kem_pub (eskA i) 
     in kdf(<tagke,<<yrA,rB(j)>,<a,b>>>,kBh(j)) 
     else kdf(<tagke,<<yrA,rB(j)>,<a,b>>>,encap_shared (r' j) yepkA) 
  in out(cB,diff(keyB,kS(j))).


system [postquantum] ideal = (!_i A : A_ideal(i) | !_j B : B_ideal(j)).


(** ---------------------------------------------------------------------- *)

name kfresh : kem_shared.

(** Collision KEM *)
(** On the left *)

global lemma [ideal/left,ideal/left] GcollKEML (i,j:index[const], k:index):
  [encap_public (r i) (kem_pub (eskA k)) =
   encap_public (r j) (kem_pub (eskA k))
   =>
   i = j].
Proof.
  nosimpl ghave Hij : [i = j || i <> j] by auto.
  case Hij; 1: auto.
  intro H.
  ghave He : [i <> j] ->
           equiv(kem_pub (eskA k),
                 diff(encap_shared (r j) (kem_pub (eskA k)),kfresh),
                 encap_public (r i) (kem_pub (eskA k)),
                 encap_public (r j) (kem_pub (eskA k)),
                 encap_shared (r i) (kem_pub (eskA k))).
  intro _; by crypto KEM_CPA_SINGLE. 

  assert (kfresh = encap_shared (r i) (kem_pub (eskA k))).
  have G := He  Hij.
project => //.    

rewrite equiv -G => //.
by rewrite !-decap_encap H.

rewrite equiv -G => //.
by rewrite !-decap_encap H.

  fresh Meq.
Qed.


lemma [set:ideal/left;equiv:ideal/left,ideal/left] collisionKEML (i,j:index[const], k: index):
  encap_public (r i) (kem_pub (eskA k)) =
   encap_public (r j) (kem_pub (eskA k))
   =>
   i = j.
Proof. 
  intro H.
  use GcollKEML with i,j,k => //. 
Qed.


(** On the right *)


global lemma [ideal/right,ideal/right] GcollKEMR (i,j:index[const], k:index):
  [encap_public (r i) (kem_pub (eskA k)) =
   encap_public (r j) (kem_pub (eskA k))
   =>
   i = j].
Proof.
  nosimpl ghave Hij : [i = j || i <> j] by auto.
  case Hij; 1: auto.
  intro H.
  ghave He : [i <> j] ->
           equiv(kem_pub (eskA k),
                 diff(encap_shared (r j) (kem_pub (eskA k)),kfresh),
                 encap_public (r i) (kem_pub (eskA k)),
                 encap_public (r j) (kem_pub (eskA k)),
                 encap_shared (r i) (kem_pub (eskA k))).
  intro _; by crypto KEM_CPA_SINGLE. 

  assert (kfresh = encap_shared (r i) (kem_pub (eskA k))).
  have G := He  Hij.
project => //.    

rewrite equiv -G => //.
by rewrite !-decap_encap H.

rewrite equiv -G => //.
by rewrite !-decap_encap H.

  fresh Meq.
Qed.


lemma [set:ideal/right;equiv:ideal/right,ideal/right] collisionKEMR (i,j:index[const], k: index):
  encap_public (r i) (kem_pub (eskA k)) =
   encap_public (r j) (kem_pub (eskA k))
   =>
   i = j.
Proof. 
  intro H.
  use GcollKEMR with i,j,k => //. 
Qed.



lemma [any] eq_eq['a]: forall (x,y:'a), x = y => x=y.
Proof.
auto.
Qed.


lemma [ideal] introTryFind :
  forall x:message, forall m:index -> message, 
   x = try find j such that x = m j in m j else x. 
Proof.
intro x. intro m.
by case(try find j such that _ in m j else x).
Qed.

(** pk injectivity *)

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

lemma [any] tryFind(i:index,j0:index) :
  try find (i0:index) such that (kem_pub(eskA(i)) = kem_pub(eskA(i0))) 
           in (encap_public (r j0) (kem_pub (eskA i))) 
           else encap_public (r' j0) (kem_pub (eskA i)) 
  = encap_public (r j0) (kem_pub (eskA i)).
Proof.
 by use tryFind0 with i,(fun (i:index) => fun (i0:index) => encap_public (r j0) (kem_pub (eskA i))),(fun (i:index) => encap_public (r' j0) (kem_pub (eskA i))).
Qed.


lemma [ideal] KMacAgreement : (forall i:index, forall j:index,
 happens(A1(i)) && happens(B1(j)) && 
 input@B(j) = kem_pub(eskA i) && output@B(j) = input@A1(i) => 
  kmacB@B1(j) = kmacA@A1(i)).
Proof.
  intro i j [HapA HapB HinputBj HoutputBj]. 
  rewrite /kmacA /kmacB /epkA.  rewrite  -HoutputBj  HinputBj. 
  use depends_B_B1 with j; [2:constraints].
  rewrite /output.
  rewrite /c HinputBj. rewrite tryFind. use tryFind0 with i, (fun (i:index) => fun (i0:index) => kdf
    (<tagmac,<kem_pub (eskA i),encap_public (r j) (kem_pub (eskA i))>>,
     kBh j) ), (fun (i:index) => kdf
    (<tagmac,<kem_pub (eskA i),encap_public (r j) (kem_pub (eskA i))>>,
     encap_shared (r' j) (kem_pub (eskA i)))) . rewrite Meq. simpl.
  case (try find (j0:index) such that _ in kdf(_,_) else _).
  ++ intro [j0 [Henc Hsimple]]. rewrite Hsimple.  clear Hsimple. clear Meq.
      project. 
          - use collisionKEML with j, j0, i.  assert (j=j0) => //.  
          - use collisionKEMR with j, j0, i.  assert (j=j0) => //.

  ++ intro [Henc Hsimple]. clear Hsimple. use Henc with j.  auto. constraints. 
Qed.

(** Well-authentication A *)

lemma [ideal] WauthA_iff :
forall (tau:timestamp), forall (i:index),
happens(tau) && (tau = A2(i) || tau = A3(i)) =>
   (xB@tau = b &&
    checksign (<tag0,<<epkA@A(i),input@A1(i)>,<rA(i),xrB@tau>>>, xsigmaB@tau,vk (skB)) &&
         mac (<tag0,b>, kmacA@A1(i)) = xmacB@tau) 
    <=> exists j:index, (B1(j) < tau
               && fst(output@B1(j)) = fst(input@tau)
               && fst(snd(output@B1(j))) = fst(snd(input@tau))
               && fst(snd(snd(output@B1(j)))) = fst(snd(snd(input@tau)))
               && snd(snd(snd(output@B1(j)))) = snd(snd(snd(input@tau)))
               && A1(i) < tau   && output@A1(i) = input@B1(j)
               && B(j)  < B1(j) && output@B(j)  = input@A1(i)
               && A(i)  < A1(i) && output@A(i) = input@B(j)).

Proof.
intro tau. intro i [Hap HapA]. 

assert(A1(i) < tau). { destruct HapA as [_|_]. 
       + use depends_A1_A2 with i; constraints. 
       + use depends_A1_A3 with i; constraints. 
}

use depends_A_A1 with i; [2:constraints].   

assert(epkA@A(i) = kem_pub (eskA i)) as Exp_epkA by destruct HapA as [_|_]; rewrite /epkA. 

split.

* (** => *)
intro HcondA. destruct HcondA as [EqA EqSignA EqMacA].

euf EqSignA. intro [j0 [HA1 HA2]].
assert (B1(j0) < tau). { constraints. }

clear HA1. rewrite /c in HA2. 

assert(input@B(j0) = kem_pub (eskA i)) as HinputB. 
  {clear EqMacA EqSignA. destruct HapA as [_|_]. congruence. congruence. }.
rewrite HinputB tryFind in HA2.
use depends_B_B1 with j0; [2: constraints].
exists j0. rewrite /output. repeat split; [1,6,8, 10: constraints | 7,11: congruence ].
  + by destruct HapA as [HapA1 | HapA2].
  + by destruct HapA as [HapA1 | HapA2]. 
  + rewrite /sigmaB. 
   use sufcma with <tag0,<<epkA@A(i),input@A1(i)>,<rA(i),xrB@tau>>>,xsigmaB@tau,skB as EqCMA => //. 
   rewrite /c HinputB tryFind. simpl. by destruct HapA as [_ | _].
  + rewrite /macB. assert(input@A1(i) = encap_public (r j0) (kem_pub (eskA i))) as HinputA1 by auto.
    assert( kmacA@A1(i) = kdf(<tagmac,<kem_pub (eskA i),input@A1(i)>>, kBh j0 )) as HkA. {
      rewrite /kmacA HinputA1 /epkA.
      assert(forall j:index, 
        encap_public (r j0) (kem_pub (eskA i)) = encap_public (r j) (kem_pub (eskA i)) <=> j = j0). intro j. split.   
      project.   
             use collisionKEML with j, j0, i => //.   
             use collisionKEMR with j, j0, i => //.   
             auto.

      case (try find (j:index) such that  (encap_public (r j0) (kem_pub (eskA i)) =
   encap_public (r j) (kem_pub (eskA i)))  in kdf(_,_) else _).
      - intro [j [Henc Hsimple]].  rewrite Hsimple. case(j=j0). auto. intro Neq. use H with j. destruct H0 as [H1 H2]. auto. 
      - intro [Hn _]; by use Hn with j0.
    }. simpl.
    destruct HapA as [HapA1 | HapA2].
     rewrite /kmacB. rewrite HapA1 in EqMacA. rewrite /xmacB in EqMacA. 
rewrite HapA1. rewrite /c !HinputB. rewrite tryFind -HinputA1 -HkA. 
use tryFind0 with i,(fun (i:index) => fun (i0:index) => (kmacA@tau)),(fun (i:index) =>kdf
       (<tagmac,<kem_pub (eskA i),input@A1(i)>>,
        encap_shared (r' j0) (kem_pub (eskA i)))).
rewrite Meq. simpl. auto. 
     rewrite /kmacB. rewrite HapA2 in EqMacA. rewrite /xmacB in EqMacA. 
rewrite HapA2. rewrite /c !HinputB. rewrite tryFind -HinputA1 -HkA. 
use tryFind0 with i,(fun (i:index) => fun (i0:index) => (kmacA@tau)),(fun (i:index) =>kdf
       (<tagmac,<kem_pub (eskA i),input@A1(i)>>,
        encap_shared (r' j0) (kem_pub (eskA i)))).
rewrite Meq. simpl. auto. 
  + by rewrite /c HinputB tryFind.

 
* (** <= *)
  intro [j [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11]].

  clear H10. clear H8. clear H6. clear Exp_epkA. clear Clt.
  use depends_B_B1 with j; [2 : constraints].
  use KMacAgreement with i,j as KMacAgreement1.

  rewrite -KMacAgreement1. 
  destruct HapA as [HapA2 | HapA3]. 
   + rewrite HapA2; expandall; simpl; congruence.
   + rewrite HapA3; expandall; simpl; congruence.

  rewrite /output /epkA in H11.
  repeat split;  [1,2,3,4: constraints].
Qed.


lemma [ideal] WauthA_eq :
forall (tau:timestamp), forall (i:index),
happens(tau) && (tau = A2(i) || tau = A3(i)) =>
  (cond@tau = (tau = A2(i))) =
       exists (j:index), 
             ( B1(j) < tau
             && fst(output@B1(j)) = fst(input@tau)
             && fst(snd(output@B1(j))) = fst(snd(input@tau))
             && fst(snd(snd(output@B1(j)))) = fst(snd(snd(input@tau)))
             && snd(snd(snd(output@B1(j)))) = snd(snd(snd(input@tau)))
             && A1(i) < tau   && output@A1(i) = input@B1(j)
             && B(j)  < B1(j) && output@B(j)  = input@A1(i)
             && A(i)  < A1(i) && output@A(i) = input@B(j)).
Proof.
  intro tau i. 
  intro [Hap Htau]. rewrite eq_iff.
  use WauthA_iff with tau,i as WA.
  destruct Htau as [Htau|Htau]; try (rewrite /cond Htau in *; by rewrite WA).
  rewrite /cond Htau. assert((A3(i) = A2(i)) = false) as -> by auto.
  rewrite not_eqfalse not_not. rewrite Htau in *; by rewrite WA.
  auto.
Qed.


lemma [ideal] axA2_input_A1 : forall (i:index),
  happens(A2(i)) =>  cond@A2(i) => exists j0:index,forall t:message, forall m: index -> message, 
   try find j such that input@A1(i) = encap_public (r j) (kem_pub (eskA i)) in m j else t = m j0.
Proof.
intro i. intro Ha Hc.
use WauthA_eq with A2(i),i as WA; [2: auto].  rewrite Hc in WA; clear Hc; simpl.
destruct WA as [j [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11]]. exists j.
expand output@B(j). expand output@A(i). rewrite /c /epkA -H11 in *.
rewrite tryFind in H9. rewrite -H9.
intro t m.
case (try find (j0:index) such that _ in m j0 else t).
+ intro [j0 [Heq Htf]]. rewrite Htf. case (j=j0). intro *. congruence.
  intro Neq. 
  clear H2 H3 H4 H5 H7 H9.
  project.
  use collisionKEML with j, j0, i.  auto.
  use collisionKEMR with j, j0, i. auto.

+ intro [Habsurd _]. by use Habsurd with j. 
Qed.

lemma [ideal] WauthB_iff :
  forall tau:timestamp, forall (j:index),
  (happens(tau) && (tau = B2(j) || tau = B3(j)) && exec@pred(tau)) =>
  (exec@pred(tau) && happens(tau) && 
yA@tau = a &&
checksign (<tag1,<<input@B(j),c@B(j)>,<input@B1(j),rB j>>>,
           ysigmaA@tau, vk (skA)) &&
mac (<tag1,a>, kmacB@B1(j)) = ymacA@tau ) <=>
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

intro tauB j.
intro [Hap HtauB Hexec].
(** Lemmas used to avoid case split in further proof *)
(** dependency *)
assert(B1(j) < tauB) by destruct HtauB as [HtauB2 | HtauB3]; depends B1(j), tauB.

(** expansions *)
assert( ysigmaA@tauB = fst(snd(input@tauB)) ) as Exp_ysigmaA
 by destruct HtauB as [HtauB2 | HtauB3]; try expand ysigmaA@tauB.

assert(ymacA@tauB = snd (snd (input@tauB))) as Exp_ymacA 
 by destruct HtauB as [_|_]; try expand ymacA@tauB.

assert(yA@tauB = fst(input@tauB)) as Exp_yA
 by destruct HtauB as [_|_]; try expand yA@tauB.

assert(kmacB@tauB = kmacB@B1(j) ) as Exp_kmacB
 by destruct HtauB as [_|_]; try expand kmacB@tauB.

 split.

* (** => *) (** slow part of the proof *)
rewrite Hexec Hap; simpl.
intro Hcond. destruct Hcond as [EqB EqSignB EqMacB].
 
rewrite Exp_ysigmaA in *. clear Exp_ysigmaA.

euf EqSignB. 
intro [i [H1 H2]]. exists i.

assert (A2(i) < tauB) by (destruct H1 as [H11| H12|H13] => //; depends B(j), B1(j) => //).

use executability with pred(tauB) as executable; [2,3:constraints].
use executable with A2(i) as  [HexecpA2 HcondA2]; [2: constraints].  clear executable.
use WauthA_iff with A2(i),i as [HL HR]; [2:constraints].   (** this command takes long to execute *) 
expand cond@A2(i).
use HL with HcondA2 as [j0 [Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7 Ha8 Ha9 Ha10 Ha11]].
clear HL. clear HcondA2.
assert(j0 = j). clear HR. clear EqSignB. clear EqMacB. destruct HtauB as [HtauB2 | HtauB3].
  - rewrite HtauB2 in *. expandall; simpl; constraints. 
  - rewrite HtauB3 in *. expandall; simpl; constraints. 
  
rewrite Ieq in *. clear Ieq.

rewrite -Ha11 in H2. rewrite /output /epkA in H2. 

clear HR.

use KMacAgreement with i,j.
use sufcma with <tag1,<<input@B(j),c@B(j)>,<input@B1(j),rB(j)>>>, fst (snd (input@tauB)), skA ; [2:constraints].

repeat split; [1,5,10,12,14: constraints | 2,3,6,7,8,9,11,13:auto]. 


rewrite /output. simpl. congruence. 
rewrite -Ha11. congruence. 

repeat split.
 - constraints.
 - constraints.
 - rewrite -Ha11 /output /epkA. constraints.
 - constraints.

* (** <= *)
  intro [i [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16]].
  assert(cond@tauB = ((yA@tauB = a && checksign(<tag1,<<input@B(j),c@B(j)>,<input@B1(j),rB j>>>,
           ysigmaA@tauB, vk (skA)) &&  mac (<tag1,a>, kmacB@B1(j)) = ymacA@tauB) = (tauB = B2(j)))) as Exp_cond.
  { rewrite eq_iff. split.
    + intro Hrw. destruct HtauB as [HB | HB].  
       rewrite /cond in Hrw. rewrite Hrw HB eq_iff. simpl. constraints. 
 rewrite /cond in Hrw. rewrite Hrw HB eq_iff. simpl. constraints. 

    + intro Hrw. destruct HtauB as [HB | HB].  rewrite /cond Hrw. constraints. rewrite /cond Hrw. constraints.

  }.

  clear Hexec. rewrite H1. rewrite Hap. 

 rewrite Exp_ysigmaA.

  use depends_B_B1 with j; [2:constraints].
  use depends_A_A1 with i; [2: constraints].


  repeat split; [1,2:constraints]. 
        + auto. 
        + destruct HtauB as [HtauB2 | HtauB3].  
              ++ rewrite HtauB2 in *.  simpl. expand cond@B2(j). expand ysigmaA@B2(j). expand output@A2(i).  rewrite -H4. expandall.  auto. 
              ++ rewrite HtauB3 in *.  simpl. expand cond@B3(j). expand ysigmaA@B3(j). expand output@A2(i).  rewrite -H4. simpl.  rewrite /xrB. rewrite -H16 /output /c /epkA -H12 -H14 /output /c. 
 auto. 
        + destruct HtauB as [HtauB2 | HtauB3].
                ++ rewrite HtauB2 in *.  simpl. expand ymacA@B2(j). rewrite -H5. rewrite /output. simpl. 
                   use KMacAgreement with i,j.  clear Exp_cond H1 H10 H12 H14 H16 H3 H4 H5 H7 H8 H9.
                   simpl. constraints.  
                   repeat split. constraints. constraints. rewrite -H16 /output /epkA; constraints. rewrite H14; constraints.
               ++ rewrite HtauB3 in *.  simpl. expand ymacA@B3(j). rewrite -H5. rewrite /output. simpl. 
                   use KMacAgreement with i,j.  clear Exp_cond H1 H10 H12 H14 H16 H3 H4 H5 H7 H8 H9.
                   simpl. constraints.  
                   repeat split. constraints. constraints. rewrite -H16 /output /epkA; constraints. rewrite H14; constraints.
Qed.


lemma [ideal] WauthB_eq :
  forall tau:timestamp, forall (j:index),
  (happens(tau) && (tau = B2(j) || tau = B3(j)) && exec@pred(tau)) =>
  (cond@tau = (tau = B2(j))) = 
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
             && A(i) < A1(i)  && output@A(i) = input@B(j)).
Proof.
  intro tau j. intro [HapTau Htau Hexec].  use WauthB_iff with tau,j as WA. 
  case Htau.
  + rewrite Htau /cond; rewrite Hexec HapTau Htau in WA; simpl; rewrite WA.
    rewrite eq_iff.  split.  intro [i Hi]. exists i.  rewrite Htau in *.  split. assumption. assumption. 
    intro [i Hi]. exists i.  rewrite Htau in *. destruct Hi as [_ Hi]. assumption. 

  + rewrite Htau /cond; rewrite Hexec HapTau Htau in WA; simpl; rewrite WA.
    assert((B3(j) = B2(j)) = false) as -> by auto.
    search (not(_) = _). rewrite -not_true eq_not. simpl.
    rewrite eq_iff.  split.  intro [i Hi]. exists i.  rewrite Htau in *.  split. assumption. assumption. 
    intro [i Hi]. exists i.  rewrite Htau in *. destruct Hi as [_ Hi]. assumption. 
    auto.
Qed.

lemma [ideal] axB2_input_B_and_B1 : forall (j:index),
  happens(B2(j)) =>  (exec@B2(j) => exists i:index,
  (forall t:message, forall m:index -> message,
  try find i0 such that input@B(j) = kem_pub (eskA i0)
  in m i0 else t = m i)
  && (input@B(j) = kem_pub (eskA i)) 
  && (input@B1(j) = (rA i))).

Proof.
 intro j HapB2 Hexec. use WauthB_eq with B2(j),j as WA. simpl.
 expand exec@B2(j). expand cond@B2(j).
 destruct Hexec as [Hexec Hcond]. rewrite Hcond in WA. simpl.
 destruct WA as [i [WA1 WA2 WA3 WA4 WA5 WA6 WA7 WA8 WA9 WA10 WA11 WA12 WA13 WA14 WA15 WA16]].
 exists i. rewrite -WA16. rewrite /output /epkA.
 assert(forall (t:message,m:index -> message),
  try find i0:index such that (kem_pub (eskA i) = kem_pub (eskA i0)) in m i0 else t =
  m i) as GenConc.
 {
  intro t. intro m. case (try find (i0:index) such that (kem_pub (_) = _) in m i0 else t).
  ++ intro [i0 [Heq Htf]]. rewrite Htf. assert(i = i0). {
       use pk_injectivity with i,i0 as pk_inj. 
       rewrite Heq in pk_inj. simpl. 
       by rewrite -eq_iff in pk_inj. 
     }. 
    rewrite  Ieq. constraints.
  ++ intro [Habsurd _]. by use Habsurd with i.
 }.
 by rewrite GenConc.
 auto.
Qed.


(************** STRONG SECRECY *****************)

name key : message.

lemma [any] neq_leq_leq_pred(t,t':timestamp) : t<>t' => ((t<=t') <=> (t<= pred(t'))).
Proof.
 auto.
Qed.

lemma [ideal] ITF_A1: forall i:index, try find j such that input@A1(i) = encap_public (r j) (kem_pub (eskA i)) in encap_public (r j) (kem_pub (eskA i)) else input@A1(i) = input@A1(i).
Proof. 
 intro i. by case (try find (j:index) such that _ in _ else input@A1(i)).
Qed.

global theorem [ideal] StrongSecrecy(tau:timestamp[const]) :
[happens(tau)]->
  equiv((skA,skB,frame@tau,a,b),
        seq(i,j:index => ((kem_pub (eskA i)),
        (** Data from honest exchange. *) 
        encap_public (r j) (kem_pub (eskA i)),
        (r' j),
        kdf(<tagmac,<kem_pub (eskA i),encap_public (r j) (kem_pub (eskA i))>>,kBh(j)),
        rA(i), rB(j)
        ))).

Proof.
intro HapTau.


induction tau; intro *.

(** init *)
*  rewrite /frame. refl.

(** A *)
* rewrite /frame /state /transcript /output /exec /cond.  fa 0. fa (_,_,_). fa !<_,_>.
  rewrite /input. fa (if _ then _ else _). rewrite /epkA. fa 3. simpl. fa(qatt _). { auto. }
  by apply IH.

(** A1 *)
* rewrite /frame /state /transcript /output /exec /cond.  fa 0. fa (_,_,_). fa !<_,_>.
  rewrite /input. fa (if _ then _ else _). fa 3. simpl. fa(qatt _). { auto. }
  by apply IH.

(** A2 *)
(** 1/ prove a lemma WauthA *)
(** 2/ rewrite under exec@A2 using WauthA *)
(** 3/ get rid of cond@A2 with fadup *)

* rewrite /frame /state /transcript.  fa 0. fa (_,_,_). fa !<_,_>. simpl.
 
  (** output *)
  assert(if exec@A2(i) then output@A2(i)
   = if exec@A2(i) then
     try find j:index such that (input@A1(i) = encap_public (r j) (epkA@A(i)))
     in 
     <a,
      <sign (<tag1,
              <<epkA@A(i),input@A1(i)>,<rA i,fst (snd (input@A2(i)))>>>,
             skA),
       mac (<tag1,a>,kdf (<tagmac,<epkA@A(i),encap_public (r j) (epkA@A(i))>>, kBh j))>>) as aux_A2_output.
  { rewrite /output.
    case cond@A2(i) => //.
    + intro Hcond. use axA2_input_A1 with i as [j0 ax1] => //.
       by rewrite !ax1 -ITF_A1 !ax1 => //. 
    + intro Hcond. expand exec@A2(i). rewrite !if_false => //; try rewrite not_and => //; by right.
  }.
  rewrite aux_A2_output in 7. fa (if _ then _). expand epkA@A(i). deduce 7. clear aux_A2_output.  

  (** exec *)
  expand exec@A2(i).
  use WauthA_eq with A2(i),i as WA; 2: auto.
  rewrite eq_assoc in WA. rewrite WA in 6. clear WA.
  assert((A2(i) = A2(i)) = true) => //.
  rewrite H in 6.  
  deduce 6.
  
  rewrite /input. fa 3. fa(qatt _). {auto. }
  by apply IH.

(** A3 *)
(** 1/ prove a lemma WauthA *)
(** 2/ get rid of cond@A3 *)
* rewrite /frame /state /transcript /output. fa 0. fa (_,_,_). fa !<_,_>. simpl.
  expand exec@A3(i).
  use WauthA_eq with A3(i),i as WA; 2: auto.
  rewrite eq_assoc in WA. rewrite WA in 6. clear WA. deduce 6. 

  rewrite /input. fa 3. fa(qatt _). {auto. }
  by apply IH.


(** B *)
* rewrite /frame /state /transcript /exec /cond /output /c.
 fa 0. fa (_,_,_). fa !<_,_>. simpl.  
 fa 7. (*if exec then *)

  assert(
     try find i :index such that (input@B(j) = kem_pub (eskA i))
     in encap_public (r j) (input@B(j))
     else encap_public (r' j) (input@B(j)) =
     try find i :index such that (input@B(j) = kem_pub (eskA i))
     in encap_public (r j) (kem_pub (eskA i))
     else encap_public (r' j) (input@B(j))).  
rewrite (eq_eq (encap_public (r j) (kem_pub (eskA _))) (encap_public (r j) (input@B(j)))) => //.
rewrite H in 7.
clear H.  
fa 7. 
fa 9. fa 7.  rewrite /input. fa 3. fa(qatt _). { auto. }
apply IH.
 
(** case B1 *)
* rewrite /frame /state /transcript /output. fa 0. fa (_,_,_). fa !<_,_>. simpl.

  fa (if _ then _). rewrite /exec /cond. fa !<_,_>.

 (** sign *)
  rewrite /sigmaB /c. 
  fa sign(_,_). fa !<_,_>.
  assert(
     try find i:index such that (input@B(j) = kem_pub (eskA i))
     in encap_public (r j) (input@B(j))
     else encap_public (r' j) (input@B(j)) =
     try find i:index such that (input@B(j) = kem_pub (eskA i))
     in encap_public (r j) (kem_pub (eskA i))
     else encap_public (r' j) (input@B(j))).  

rewrite (eq_eq (encap_public (r j) (kem_pub (eskA _))) (encap_public (r j) (input@B(j)))) => //.
rewrite H in 9.
deduce 9.

(** mac *)
  rewrite /macB /kmacB.
 fa mac(_,_).


  assert( c@B(j) = 
   try find i:index such that (input@B(j) = kem_pub (eskA i))
   in encap_public (r j) (kem_pub (eskA i))
   else (if forall (i:index), input@B(j) <> kem_pub(eskA i) then  encap_public (r' j) (input@B(j)))) as Htf.
  { expand c@B(j).
    case (try find i:index such that _ in _ else encap_public _ _).
    ++ intro [i [Heq Htf]]. rewrite Htf. rewrite Heq. 
       case(try find i0:index such that _ in encap_public _ _  else _).
       +++ intro [i0 [Heq0 Htf0]].  rewrite Htf0. by rewrite pk_injectivity in Heq0.
       +++ intro [Hneq _]. by use Hneq with i. 
    ++ intro [Hneq Htf]. 
       case (try find i:index such that _ in encap_public _ _  else _).
       +++ intro [i0 [Heq _]]. rewrite Heq in Hneq. by use Hneq with i0.
       +++ intro [Hneq1 Htf1]. rewrite not_eq in Hneq. by rewrite Hneq if_true.
 }. 
  rewrite !Htf. 

clear Htf.

assert( try find i:index such that (input@B(j) = kem_pub (eskA i))
   in
     kdf
       (<tagmac,
         <input@B(j),
          try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        kBh j)
   else
     kdf
       (<tagmac,
         <input@B(j),
          try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        encap_shared (r' j) (input@B(j)))
=
 try find i:index such that (input@B(j) = kem_pub (eskA i))
   in
     kdf
       (<tagmac,
         <kem_pub (eskA i),
          try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        kBh j)
   else
     kdf
       (<tagmac,
         <input@B(j),
          try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        encap_shared (r' j) (input@B(j)))

).

rewrite (eq_eq (kdf(<tagmac, < (kem_pub (eskA _)),  try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        kBh j))  (kdf(<tagmac, < (input@B(j)),  try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        kBh j))) => //.
rewrite H0 in 9.
clear H0. clear H.
assert(try find i:index such that (input@B(j) = kem_pub (eskA i))
   in
     kdf
       (<tagmac,
         <kem_pub (eskA i),
          try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        kBh j)
   else
     kdf
       (<tagmac,
         <input@B(j),
          try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        encap_shared (r' j) (input@B(j)))
=
try find i:index such that (input@B(j) = kem_pub (eskA i))
   in
     kdf
       (<tagmac,
         <kem_pub (eskA i),
  encap_public (r j) (kem_pub (eskA i))
>>,
        kBh j)
   else
     kdf
       (<tagmac,
         <input@B(j),
          try find i:index such that (input@B(j) = kem_pub (eskA i))
          in encap_public (r j) (kem_pub (eskA i))
          else
            (if (forall (i:index), input@B(j) <> kem_pub (eskA i)) then
               encap_public (r' j) (input@B(j)))>>,
        encap_shared (r' j) (input@B(j)))

).

  case (try find (i:index) such that (input@B(j) = kem_pub (eskA i))  in kdf(_,_)  else kdf(_,_)).
  + intro  [ij [Hi Hm]]. rewrite Hm.   case (try find (i:index) such that (input@B(j) = kem_pub (eskA i))  in encap_public _ _ else _).
intro [ij' [Hi' Hm']]. rewrite Hm'.  case (try find (i:index) such that (input@B(j) = kem_pub (eskA i))  in kdf(_,_)  else kdf(_,_)).
intro [ij'' [Hi'' Hm'']]. rewrite Hm''. auto.
intro [Hn'' _]. by use Hn'' with ij.
intro [Hn' _]. by use Hn' with ij.
 + intro [Hn _].  case (try find (i:index) such that (input@B(j) = kem_pub (eskA i))  in kdf(_,_)  else kdf(_,_)).
intro [ij' [Hi' Hm']].
 rewrite Hm'. by use Hn with ij'. 
intro [Hyp1 Hyp2]. auto. 
rewrite H in 9.
clear H.
fa 6.


fa 9. fa 9. fa 11. fa !<_,_>. fa 11.  fa 11. fa 12.  fa 13. 
deduce 12.
expand input@B1(j). 
have Ord :=  depends_B_B1 j.
fa 3. fa(qatt _). {auto. }
apply IH.


(** case B2 *)
* rewrite /frame /transcript /output. fa 0. fa (_,_,_). fa !<_,_>. simpl.   
  rewrite /keyB.
assert(if exec@B2(j) then
     diff(
       try find i:index such that (input@B(j) = kem_pub (eskA i))
       in kdf (<tagke,<<input@B1(j),rB j>,<a,b>>>, kBh j)
       else
         kdf
           (<tagke,<<input@B1(j),rB j>,<a,b>>>,
            encap_shared (r' j) (input@B(j))), kS j)
= 
if exec@B2(j) then
     diff(  
        kdf (<tagke,<<input@B1(j), rB j>,<a,b>>>, kBh j), kS j)
).
 case exec@B2(j);2:auto. intro Hexec.  simpl. 
 use axB2_input_B_and_B1 with j, HapTau.   
 destruct H as [i [H1 H2 H3]].
use H1 with  kdf(<tagke,<<input@B1(j),rB j>,<a,b>>>,
         encap_shared (r' j) (input@B(j))), (fun (i:index) => kdf (<tagke,<<input@B1(j),rB j>,<a,b>>>, kBh j)).

rewrite Meq. simpl.   auto. 
auto.

rewrite H in 7.
fa 7.


use WauthB_eq with B2(j),j as WA. 
rewrite eq_assoc in WA.
  rewrite /exec WA in 6; [1: intro *; repeat split; constraints].
clear WA. clear H. 
have Ord := depends_B1_B2 j.
prf 7. repeat split. 
 + intro *. use tagke_tagmac_neq; [1: congruence].  
 + intro *; use tagke_tagmac_neq; [1: congruence].
 + intro *; use tagke_tagmac_neq; [1: congruence].
 + intro *; use tagke_tagmac_neq; [1: congruence].
 + intro i j0 [HB1 | HB2 | HB3 | HB4 | HB5 | HB6].
    ++ intro *. rewrite Ieq in *. use depends_B1_B2 with j0; [1,2: constraints]. 
    ++ intro *. rewrite Ieq in *. constraints.
    ++ intro *. rewrite Ieq in *. use depends_B_B1 with j0;  [1,2: constraints].
    ++ intro *. rewrite Ieq in *.  use depends_B_B1 with j0; [1,2: constraints].
    ++ intro *. rewrite Ieq in *. constraints.
    ++ intro *. rewrite Ieq in *. use depends_B1_B2 with j0; [1,2: constraints].

 + intro *; use tagke_tagmac_neq; [1: congruence].
 + intro *; use tagke_tagmac_neq; [1: congruence].
 + intro *; use tagke_tagmac_neq; [1: congruence].

fresh 7.
intro j0.
intro [HB1 | HB2 | HB3 | HB4 | HB5 | HB6].  constraints. constraints. 
destruct HB3 as [i HB3]. use depends_B_B1 with j; [1,2:constraints].   constraints.
constraints. constraints.
deduce 6. 

rewrite /input /state. fa 3. fa(qatt _). {constraints. }.
apply IH. 

(** B3 *)
* rewrite /frame /state /transcript /output. fa 0. fa (_,_,_). fa !<_,_>. simpl.
  use WauthB_eq with B3(j),j as WA. rewrite eq_assoc in WA.
  rewrite /exec WA in 6. clear WA. constraints. 
  deduce 6. 
  rewrite /input. fa 3. fa(qatt _). { constraints.  }
apply IH.
Qed.
