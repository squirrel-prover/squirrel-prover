(** Long-term keys:
   - skA, skB signature keys for A and B

   Session keys:
   - A: eskA, rA
   - B: kB, r, rB

   Transcripts:
   - t2 = [epkA,enc(kB,r,epkA)]
   - t4 = [epkA,enc(kB,r,epkA),rA,rB]

   Tags tagke and tagmac are assumed to be distinct constants.
   Tags tag0, tag1 and identities a and b are arbitrary constants:
   we do not need any assumptions on these due for the scenario
   considered here.

   A->B: pk(eskA) =def epkA
   B->A: enc(kB,r,epkA)
   both compute kmac = kdf(<tagmac,t2>,kB)
   A->B: rA
   B->A: b, rB, sign(<tag0,t4>,skB), mac(<tag0,b>,kmac)
   A->B: a,     sign(<tag0,t4>,skA), mac(<tag1,a>,kmac)

   Both finally compute kdf(<tagke,<<rA,rB>,<a,b>>>,kB). *)

(** -------------------------------------------------------- *)

(** ## KEM primitives, with functionality axiom and CPA game *)

(** The KEM relies on a secret/public keypair.

    The public key is generated using `kem_pub` from the secret key.

    Then `encap` is a randomized primitive (with explicit randomness
    as usual) that takes a public key and returns a pair composed of:
    - a shared secret;
    - a public encapsulation.
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
type kem_shared[large,serializable].

abstract kem_pub : kem_skey -> message.
abstract encap : kem_randomness -> message -> kem_shared * message.
abstract decap : message -> kem_skey -> kem_shared.

exact axiom [any] decap_encap (r:kem_randomness,k:kem_skey) :
  decap (encap r (kem_pub k) # 2) k = (encap r (kem_pub k) # 1).
hint rewrite decap_encap.

abstract format ['a] : 'a -> message.
abstract parse  ['a] : message -> 'a.
axiom [any] formatting_kem_randomness (x:kem_randomness) : parse (format x) = x.
axiom [any] formatting_kem_shared     (x:kem_shared)     : parse (format x) = x.

(** CPA game for KEMs as in, e.g.,
    <https://eprint.iacr.org/2020/1364.pdf> or <https://eprint.iacr.org/2018/903.pdf>.
    This corresponds to the strong secrecy of the shared secret
    `encap r (kem_pub skey) # 1` even when the public encapsulation is revealed. *)
game KEM_CPA = {
  rnd skey : kem_skey;
  oracle o_pub = {
    return (kem_pub skey)
  }
  oracle o_encap = {
    rnd r : kem_randomness;
    rnd s : kem_shared;
    return (encap r (kem_pub skey) # 2,
            diff(encap r (kem_pub skey) # 1, s))
  }
}.

system dummy = null.

(** In our protocol with aenc we considered an equivalence involving
    `aenc diff(kB,kfresh) pk` now we will have `diff(encap r pk # 2, kfresh)`.
    Below are some tests illustrating simplified versions of the core
    cryptographic reasoning on these terms. *)

name test_k : kem_skey.
name test_r : index->kem_randomness.
name test_f : index->kem_shared.

(** We have to enrich to help `crypto` identify the oracle call. *)
global lemma [dummy] _ (i:index[const]) :
  equiv(diff(encap (test_r i) (kem_pub test_k) # 1, test_f i)).
Proof.
  enrich (encap (test_r i) (kem_pub test_k) # 2,
          diff(encap (test_r i) (kem_pub test_k) # 1, test_f i)).
  deduce 1.
  crypto KEM_CPA (skey : test_k).
Qed.

(** This can be simplified by splitting o_encap in two oracles,
    moving the kem_randomness to a global sampling in the game. *)

game KEM_CPA_SINGLE = {
  rnd skey : kem_skey;
  rnd r : kem_randomness;
  rnd s : kem_shared;
  oracle o_pub = {
    return (kem_pub skey)
  }
  oracle o_encap_shared = {
    return diff(encap r (kem_pub skey) # 1, s)
  }
  oracle o_encap_public = {
    return (encap r (kem_pub skey) # 2)
  }
}.

global lemma [dummy] _ (i:index[const]) :
  equiv(diff(encap (test_r i) (kem_pub test_k) # 1, test_f i)).
Proof.
  crypto KEM_CPA_SINGLE.
Qed.

(** KEM_CPA also works nicely in a sequence -- which does not make
    sense with KEM_CPA_SINGLE. *)
global lemma [dummy] _ :
  equiv(fun i => diff(encap (test_r i) (kem_pub test_k) # 1,
                      test_f i)).
Proof.
  enrich (fun i =>
            (encap (test_r i) (kem_pub test_k) # 2,
             diff(encap (test_r i) (kem_pub test_k) # 1, test_f i))).
  deduce 1.
  crypto KEM_CPA (skey : test_k).
  auto.
Qed.

(** Utilities to work around limitations with tuples. *)

abstract encap_public : kem_randomness -> message -> message.
axiom [any] encap_public_spec : forall x y, encap_public x y = (encap x y # 2).

abstract encap_shared : kem_randomness -> message -> kem_shared.
axiom [any] encap_shared_spec : forall x y, encap_shared x y = (encap x y # 1).

lemma [any] decap_encap_public :
  forall x y, decap (encap_public x (kem_pub y)) y = encap_shared x (kem_pub y).
Proof.
  by rewrite encap_public_spec encap_shared_spec decap_encap.
Qed.

(** -------------------------------------------------------- *)

set processStrictLetMode = true.

(** ## Protocol model *)

(** aenc enc,dec,pk *)
signature sign, checksign, vk.
hash kdf where k:kem_shared.
hash mac.

abstract a:message.
abstract b:message.

abstract tag1: message.
abstract tag0: message.
abstract tagke: message.
abstract tagmac: message.


(** Long-term keys *)
name skA: message.
name skB: message.

(** Session keys for idealized B, which idealized A must know. *)
name kBh: kem_shared.
name r :kem_randomness.
name r':kem_randomness.
name rB: message.
name kfresh: message.
name kS: message.

channel cA.
channel cB.
name eskA : kem_skey.
name rA : message.

(** Processes A and B - Real *)
process A_real =
  let epkA = kem_pub eskA in
  out(cA,epkA);
  in(cA,xc);
  let kmacA = kdf(<tagmac,<epkA,xc>>, decap xc eskA) in
  out(cA,rA);
  in(cA,x);
  (* x = <xB,<xrB,<xsigmaB,xmacB>>> *)
  let xB = fst(x) in
  let xrB = fst(snd(x)) in
  let xsigmaB = fst(snd(snd(x))) in
  let xmacB = snd(snd(snd(x))) in
  if xB = b &&
     checksign(<tag0,<<epkA,xc>,<rA,xrB>>>, xsigmaB,vk(skB)) &&
     mac(<tag0,b>,kmacA) = xmacB then
  out(cA, <a,<sign(<tag1,<<epkA,xc>,<rA,xrB>>>,skA), mac(<tag1,a>,kmacA)>>).

process B_real =
  in(cB,yepkA);
  let c =
    if yepkA = kem_pub eskA then
      encap_public r yepkA
    else
      (* Using a different random here to ease proof. *)
      encap_public r' yepkA
  in
  let kB =
    if yepkA = kem_pub eskA then
      encap_shared r yepkA
    else
      (* Using a different random here to ease proof. *)
      encap_shared r' yepkA
  in
  out(cB,c);
  in(cB,yrA);
  let kmacB = kdf(<tagmac,<yepkA,c>>,kB) in
  let sigmaB = sign(<tag0,<<yepkA,c>,<yrA,rB>>>,skB) in
  let macB = mac(<tag0,b>,kmacB) in
  out(cB,<b,<rB,<sigmaB,macB>>>);
  in(cA,y);
  let yA = fst(y) in
  let ysigmaA = fst(snd(y)) in
  let ymacA = snd(snd(y)) in
  if yA=a &&
     checksign(<tag1,<<yepkA,c>,<yrA,rB>>>,ysigmaA,vk(skA)) &&
     mac(<tag1,a>,kmacB) = ymacA then
  let keyB = kdf(<tagke,<<yrA,rB>,<a,b>>>,kB) in
  out(cB, diff(keyB,kS)).

(** Processes A and B - Ideal *)
process A_ideal =
  let epkA = kem_pub eskA in
  out(cA,epkA);
  in(cA,xc);
  let kmacA =
    if xc = encap_public r epkA then
      (* Use kB instead of kfresh. *)
      kdf(<tagmac,<epkA,xc>>,kBh)
    else
      kdf(<tagmac,<epkA,xc>>,decap xc eskA) in
  out(cA,rA);
  in(cA,x);
  (* x = <xB,<xrB,<xsigmaB,xmacB>>> *)
  let xB = fst(x) in
  let xrB = fst(snd(x)) in
  let xsigmaB = fst(snd(snd(x))) in
  let xmacB = snd(snd(snd(x))) in
  if xB = b &&
     checksign(<tag0,<<epkA,xc>,<rA,xrB>>>, xsigmaB,vk(skB)) &&
     mac(<tag0,b>,kmacA) = xmacB then
  out(cA, <a,<sign(<tag1,<<epkA,xc>,<rA,xrB>>>,skA), mac(<tag1,a>,kmacA)>>).

process B_ideal =
  in(cB,yepkA);
  let c =
    if yepkA = kem_pub eskA then
      encap_public r yepkA
    else
      (** Using a different random here to ease proof. *)
      encap_public r' yepkA
  in
  out(cB,c);
  in(cB,yrA);
  let kmacB =
    if yepkA = kem_pub eskA then
      kdf(<tagmac,<yepkA,c>>,kBh)
    else
      kdf(<tagmac,<yepkA,c>>,encap_shared r' yepkA) in
  let sigmaB = sign(<tag0,<<yepkA,c>,<yrA,rB>>>,skB) in
  let macB = mac(<tag0,b>,kmacB) in
  out(cB,<b,<rB,<sigmaB,macB>>>);
  in(cA,y);
  let yA = fst(y) in
  let ysigmaA = fst(snd(y)) in
  let ymacA = snd(snd(y)) in
  if yA=a &&
     checksign(<tag1,<<yepkA,c>,<yrA,rB>>>,ysigmaA,vk(skA)) &&
     mac(<tag1,a>,kmacB) = ymacA then
  let keyB =
    if yepkA = kem_pub eskA then
      kdf(<tagke,<<yrA,rB>,<a,b>>>,kBh)
    else
      kdf(<tagke,<<yrA,rB>,<a,b>>>,encap_shared r' yepkA)
  in
  out(cB,diff(keyB,kS)).

system [postquantum] real  = (A : A_real  | B : B_real).
system [postquantum] ideal = (A : A_ideal | B : B_ideal).

(** ---------------------------------------------------------------------- *)
axiom [any] tagke_tagmac_neq : tagke <> tagmac.

axiom [any] sufcma :
  forall (m,s,sk:message), checksign(m,s,vk(sk)) => s = sign(m,sk).
(** ---------------------------------------------------------------------- *)


exact axiom [any] eq_false2 (b:bool) : (false = b) = not b.
hint rewrite eq_false2.

lemma [any] pair_eq (x,y,x',y':message) : (<x,y> = <x',y'>) = (x = x' && y = y').
Proof. by rewrite eq_iff. Qed.

lemma [any] eq_eq ['a] (x,y:'a) : x = y => x = y.
Proof. constraints.  Qed.

lemma [any] if_tuple2 ['a 'b] (c:bool) (x,x':'a) (y,y':'b) :
  if c then (x,y) else (x',y') = (if c then x else x', if c then y else y').
Proof. by case c. Qed.


(******************************************************)
(** Well-authentication on the real system regarding A *)
(******************************************************)


theorem [real] R_WauthA_iff :
  forall (tau:timestamp),
  happens(tau) && (tau = A2 || tau = A3) =>
   (xB@tau = b &&
    checksign (<tag0,<<epkA@A,input@A1>,<rA,xrB@tau>>>, xsigmaB@tau,vk (skB)) &&
    mac (<tag0,b>, kmacA@A1) = xmacB@tau)
   <=>
   (B1 < tau &&
    fst(output@B1) = fst(input@tau) &&
    fst(snd(output@B1)) = fst(snd(input@tau)) &&
    fst(snd(snd(output@B1))) = fst(snd(snd(input@tau))) &&
    snd(snd(snd(output@B1))) = snd(snd(snd(input@tau))) &&
    A1 < B1 && output@A1 = input@B1 &&
    B  < B1 && output@B  = input@A1 &&
    A  < A1 && output@A = input@B).
Proof.
  intro tau. intro [Hap Htau]. split.

  * (** First implication: test passes => honest trace *)
    intro HcondA. destruct HcondA as [EqA EqSignA EqMacA].
    euf EqSignA. rewrite !pair_eq /=.

    intro [HA1 [HinB HinA1] HinB1 HinB2].

    case Htau. 

    + rewrite Htau in *.
      rewrite /output /sigmaB /xsigmaB /kmacA /xmacB /macB /kmacB /xB /xrB /c /epkA /kB in *.
      reduce. 
      rewrite -HinB -EqMacA HinA1 -HinB1 HinB2 in *. simpl.
      repeat split.
        ++ use depends_A1_A2; constraints. 
        ++ apply  sufcma in EqSignA. constraints.
        ++  rewrite decap_encap_public. constraints.
        ++  fresh HinB1; [1: constraints  | 2: intro Ord; use depends_A1_A2;  constraints]. 
            intro Ord; use depends_A1_A3; constraints. 
       ++ use depends_B_B1; constraints.
       ++ use depends_A_A1; constraints.

 + rewrite Htau in *.
   rewrite /output  /sigmaB /xsigmaB /kmacA /xmacB  /macB /kmacB /xB /xrB /c /epkA /kB in *.
   reduce. 
   rewrite -HinB -EqMacA HinA1 -HinB1 HinB2 in *. 
   simpl.
   repeat split.
     ++ use depends_A1_A3; constraints.
     ++ apply sufcma in EqSignA. constraints.
     ++  rewrite decap_encap_public. constraints.
     ++  fresh HinB1; [1: constraints  | 2: intro Ord; use depends_A1_A2;  constraints]. 
            intro Ord; use depends_A1_A3; constraints. 
     ++ use depends_B_B1; constraints.
     ++ use depends_A_A1; constraints.

  * (** Second implication: honest trace => condition passes *)
    intro [_ _ _ _ _ _ _ _ HinA1 _ HinB].
    case Htau. 
    + rewrite Htau in *.   
      rewrite /output  HinB /sigmaB /xsigmaB /kmacA /xmacB  /macB /kmacB /xB /xrB /c /epkA /kB in *. 
      reduce.
      rewrite -HinB -HinA1 in *. 
      simpl.  
      rewrite decap_encap_public in *.  
      split;[1:  congruence| 2: constraints]. 

    + rewrite /output  HinB /sigmaB /xsigmaB /kmacA /xmacB  /macB /kmacB /xB /xrB /c /epkA /kB in *.
      reduce. 
      rewrite -HinB -HinA1 in *. 
      simpl. 
      rewrite decap_encap_public. 
      split; [2:constraints | 1:congruence].
Qed.


lemma [real] R_WauthA_eq :
  forall (tau:timestamp),
  happens(tau) && (tau = A2 || tau = A3) =>
  (xB@tau = b &&
   checksign (<tag0,<<epkA@A,input@A1>,<rA,xrB@tau>>>, xsigmaB@tau,vk (skB)) &&
   mac (<tag0,b>, kmacA@A1) = xmacB@tau)
  =
  (B1 < tau &&
   fst(output@B1) = fst(input@tau) &&
   fst(snd(output@B1)) = fst(snd(input@tau)) &&
   fst(snd(snd(output@B1))) = fst(snd(snd(input@tau))) &&
   snd(snd(snd(output@B1))) = snd(snd(snd(input@tau))) &&
   A1 < B1 && output@A1 = input@B1 &&
   B  < B1 && output@B  = input@A1 &&
   A  < A1 && output@A  = input@B).
Proof.
  intro H. rewrite eq_iff.
  apply R_WauthA_iff.
Qed.


(*******************************************************)
(** Well-authentication on the ideal system regarding A *)
(*******************************************************)

theorem [ideal] I_WauthA_iff :
  forall (tau:timestamp),
  happens(tau) && (tau = A2 || tau = A3) =>
   (xB@tau = b &&
    checksign (<tag0,<<epkA@A,input@A1>,<rA,xrB@tau>>>, xsigmaB@tau,vk (skB)) &&
         mac (<tag0,b>, kmacA@A1) = xmacB@tau)
    <=> (B1 < tau
               && fst(output@B1) = fst(input@tau)
               && fst(snd(output@B1)) = fst(snd(input@tau))
               && fst(snd(snd(output@B1))) = fst(snd(snd(input@tau)))
               && snd(snd(snd(output@B1))) = snd(snd(snd(input@tau)))
               && A1 < B1 && output@A1 = input@B1
               && B  < B1 && output@B  = input@A1
               && A < A1 && output@A = input@B).
Proof.
  (** The proof is almost a duplicate of the proof of R_WauthA_iff.
     We only have to change macro names, and remove a few useless steps. *)
  intro tau. intro [Hap Htau]. split.

  * (** First implication: test passes => honest trace *)
    intro HcondA. destruct HcondA as [EqA EqSignA EqMacA].
    euf EqSignA. rewrite !pair_eq /=.

    intro [HA1 [HinB HinA1] HinB1 HB1].

    case Htau.

    + rewrite Htau in *.
      rewrite /output  HinB /sigmaB /xsigmaB /kmacA /xmacB /macB /kmacB /xB /xrB /c /epkA in *.
      reduce.
      rewrite -HinB HB1 HinA1 -HinB1 in *. 
      simpl.  
      repeat split. 
        ++ use depends_A1_A2; constraints. 
        ++ apply sufcma in EqSignA. constraints. 
        ++ fresh HinB1; [1: constraints | 2: intro Ord; use depends_A1_A2; constraints].
           intro Ord; use depends_A1_A3; constraints. 
        ++  use depends_B_B1; constraints.
        ++  use depends_A_A1; constraints.

   + rewrite Htau in *.
     rewrite /output  HinB /sigmaB /xsigmaB /kmacA /xmacB /macB /kmacB /xB /xrB /c /epkA in *.
     reduce.
     rewrite -HinB HB1  HinA1 -HinB1 in *. 
     simpl.  
     repeat split. 
       ++ use depends_A1_A3; constraints. 
       ++ apply sufcma in EqSignA. constraints. 
       ++ fresh HinB1; [1: constraints | 2: intro Ord; use depends_A1_A2; constraints].
           intro Ord; use depends_A1_A3; constraints. 
       ++  use depends_B_B1; constraints.
       ++  use depends_A_A1; constraints.

 * (** Second implication: honest trace => condition passes *)

    intro [_ _ _ _ _ _ _ _ HinA1 _ HinB].
    case Htau. 
    + rewrite Htau in *.   
      rewrite /output HinB /sigmaB /xsigmaB /kmacA /xmacB /macB /kmacB /xB /xrB /c /epkA in *. 
      reduce. 
      rewrite -HinB  -HinA1 in *. 
      simpl. congruence. 

    + rewrite /output HinB /sigmaB /xsigmaB /kmacA /xmacB /macB /kmacB /xB /xrB /c /epkA in *.
      reduce.    
      rewrite -HinB -HinA1 in *. 
      simpl. 
      congruence. 
Qed.

lemma [ideal] I_WauthA_eq :
  forall (tau:timestamp),
  happens(tau) && (tau = A2 || tau = A3) =>
  (xB@tau = b &&
    checksign (<tag0,<<epkA@A,input@A1>,<rA,xrB@tau>>>, xsigmaB@tau,vk (skB)) &&
         mac (<tag0,b>, kmacA@A1) = xmacB@tau)  = ( B1 < tau
             && fst(output@B1) = fst(input@tau)
             && fst(snd(output@B1)) = fst(snd(input@tau))
             && fst(snd(snd(output@B1))) = fst(snd(snd(input@tau)))
             && snd(snd(snd(output@B1))) = snd(snd(snd(input@tau)))
             && A1 < B1 && output@A1 = input@B1
             && B  < B1 && output@B  = input@A1
             && A < A1 && output@A = input@B).
Proof.
  intro H. rewrite eq_iff.
  apply I_WauthA_iff.
Qed.


(** Corollaries of well-authentication for A *)

lemma [real/left,real/right,ideal/left,ideal/right] cond_A2_happens_B :
  happens(A2) => cond@A2 => happens(B1).
Proof.
  intro _ _. project.
   +  rewrite R_WauthA_eq in *; constraints.
   +  rewrite R_WauthA_eq in *; constraints.
   +  rewrite I_WauthA_eq in *; constraints.
   +  rewrite I_WauthA_eq in *; constraints.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] cond_A2_input_B :
  happens(A2) => cond@A2 => input@B = kem_pub eskA.
Proof.
  intro Hap Hcond.
  project.
  + rewrite R_WauthA_eq in Hcond. {constraints. } expand output@A; expand epkA@A; constraints.
  + rewrite R_WauthA_eq in Hcond. {constraints. } expand output@A; expand epkA@A; constraints.
  + rewrite I_WauthA_eq in Hcond. {constraints. } expand output@A; expand epkA@A; constraints.
  + rewrite I_WauthA_eq in Hcond. {constraints. } expand output@A; expand epkA@A; constraints.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] cond_A2_output_B :
  happens(A2) => cond@A2 => output@B = encap_public r (kem_pub eskA).
Proof.
  intro _ Hcond.
  assert happens(B1) as _. apply cond_A2_happens_B; assumption.
  assert B < B1. use depends_B_B1; assumption.  
  project. 
  + rewrite /output /c. rewrite cond_A2_input_B; [1,2:assumption]; rewrite if_true; constraints.
  + rewrite /output /c. rewrite cond_A2_input_B; [1,2:assumption]; rewrite if_true; constraints.
  + rewrite /output /c. rewrite cond_A2_input_B; [1,2:assumption];  rewrite if_true; constraints.
  + rewrite /output /c. rewrite cond_A2_input_B; [1,2:assumption]; rewrite if_true; constraints.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] cond_A2_input_A1 :
  happens(A2) => cond@A2 => input@A1 = encap_public r (kem_pub eskA).
Proof.
  intro Ha Hc.
  project.
  + rewrite R_WauthA_eq in Hc; [1: constraints]. 
     assert(input@A1 = output@B). constraints. 
     assert(input@B = output@A). constraints.  
     rewrite /output /c in Meq. rewrite /output /epkA in Meq0.
     rewrite Meq0 in Meq. simpl.  constraints.
  + rewrite R_WauthA_eq in Hc; [1: constraints].
     assert(input@A1 = output@B). constraints. 
     assert(input@B = output@A). constraints.  
     rewrite /output /c in Meq. rewrite /output /epkA in Meq0.
     rewrite Meq0 in Meq. simpl.  constraints.
  + rewrite I_WauthA_eq in Hc; [1:constraints].
     assert(input@A1 = output@B). constraints. 
     assert(input@B = output@A). constraints.  
     rewrite /output /c in Meq. rewrite /output /epkA in Meq0.
     rewrite Meq0 in Meq. simpl.  constraints.
 + rewrite I_WauthA_eq in Hc; [1:constraints].
     assert(input@A1 = output@B). constraints. 
     assert(input@B = output@A). constraints.  
     rewrite /output /c in Meq. rewrite /output /epkA in Meq0.
     rewrite Meq0 in Meq. simpl.  constraints.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] cond_A2_input_A2 :
  happens(A2) => cond@A2 => fst(snd(input@A2)) = rB.
Proof.
  intro Ha Hcond.
  project.
  + rewrite R_WauthA_eq in Hcond; [1:constraints]. expand output@B1. simpl. constraints. 
  + rewrite R_WauthA_eq in Hcond; [1:constraints]. expand output@B1. simpl. constraints.
  + rewrite I_WauthA_eq in Hcond; [1:constraints]. expand output@B1. simpl. constraints.  
  + rewrite I_WauthA_eq in Hcond; [1:constraints]. expand output@B1. simpl. constraints.  
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] exec_A2_eq (tau:timestamp) :
  happens(tau) => tau = A2 =>
  exec@tau =
  (exec@pred(tau) &&
   B1 < tau &&
   fst(output@B1) = fst(input@tau) &&
   fst(snd(output@B1)) = fst(snd(input@tau)) &&
   fst(snd(snd(output@B1))) = fst(snd(snd(input@tau))) &&
   snd(snd(snd(output@B1))) = snd(snd(snd(input@tau))) &&
   A1 < B1 && output@A1 = input@B1 &&
   B  < B1 && output@B  = input@A1 &&
   A < A1 && output@A = input@B).
Proof.
  intro _ _; project;
  rewrite /exec /cond.
  + rewrite R_WauthA_eq; auto. 
  + rewrite R_WauthA_eq; auto.
  + rewrite I_WauthA_eq; auto.
  + rewrite I_WauthA_eq; auto.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] exec_A3_eq (tau:timestamp) :
  happens(tau) => tau = A3 =>
  exec@tau =
  (exec@pred(tau) &&
   not (B1 < tau &&
        fst(output@B1) = fst(input@tau) &&
        fst(snd(output@B1)) = fst(snd(input@tau)) &&
        fst(snd(snd(output@B1))) = fst(snd(snd(input@tau))) &&
        snd(snd(snd(output@B1))) = snd(snd(snd(input@tau))) &&
        A1 < B1 && output@A1 = input@B1 &&
        B  < B1 && output@B  = input@A1 &&
        A < A1 && output@A = input@B)).
Proof.
  intro _ _; project;
  rewrite /exec /cond.
  + rewrite R_WauthA_eq; auto.
  + rewrite R_WauthA_eq; auto.
  + rewrite I_WauthA_eq; auto.
  + rewrite I_WauthA_eq; auto.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] exec_A23_eq (tau:timestamp) :
  happens(tau) => (tau = A2 || tau = A3) =>
  exec@tau =
  (exec@pred(tau) &&
   (tau = A2) =
   (B1 < tau &&
    fst(output@B1) = fst(input@tau) &&
    fst(snd(output@B1)) = fst(snd(input@tau)) &&
    fst(snd(snd(output@B1))) = fst(snd(snd(input@tau))) &&
    snd(snd(snd(output@B1))) = snd(snd(snd(input@tau))) &&
    A1 < B1 && output@A1 = input@B1 &&
    B  < B1 && output@B  = input@A1 &&
    A < A1 && output@A = input@B)).
Proof.
  intro _ [_|_].
  + project; assert (tau = A2) = true as ->;
    [1: auto | 2: simpl; rewrite exec_A2_eq; auto].
  + project; assert (tau = A2) = false as ->;
    [1: auto | 2: simpl; rewrite exec_A3_eq; auto].
Qed.

lemma [real/left,ideal/left] WauthA_eq_RI  :
  forall (tau:timestamp),
  happens(tau) && (tau = A2 || tau = A3) =>
  (diff(xB@tau,xB@tau) = b &&
   checksign (<tag0,<<epkA@A,input@A1>,<rA,xrB@tau>>>,
              xsigmaB@tau,vk (skB)) &&
   mac(<tag0,b>, kmacA@A1) = xmacB@tau)
  =
  (B1 < tau &&
   fst(output@B1) = fst(input@tau) &&
   fst(snd(output@B1)) = fst(snd(input@tau)) &&
   fst(snd(snd(output@B1))) = fst(snd(snd(input@tau))) &&
   snd(snd(snd(output@B1))) = snd(snd(snd(input@tau))) &&
   A1 < B1 && output@A1 = input@B1 &&
   B  < B1 && output@B  = input@A1 &&
   A  < A1 && output@A  = input@B).
Proof.
  intro H. rewrite eq_iff.
  project.
  + apply R_WauthA_iff; auto.
  + apply I_WauthA_iff; auto.
Qed.

lemma [ideal/right,real/right] WauthA_eq_IR:
  forall (tau:timestamp),
  happens(tau) && (tau = A2 || tau = A3) =>
  (xB@tau = b &&
   checksign (<tag0,<<epkA@A,input@A1>,<rA,xrB@tau>>>,
              xsigmaB@tau,vk (skB)) &&
   mac (<tag0,b>, kmacA@A1) = xmacB@tau)
  =
  (B1 < tau &&
   fst(output@B1) = fst(input@tau) &&
   fst(snd(output@B1)) = fst(snd(input@tau)) &&
   fst(snd(snd(output@B1))) = fst(snd(snd(input@tau))) &&
   snd(snd(snd(output@B1))) = snd(snd(snd(input@tau))) &&
   A1 < B1 && output@A1 = input@B1 &&
   B  < B1 && output@B  = input@A1 &&
   A  < A1 && output@A  = input@B).
Proof.
  intro H. rewrite eq_iff.
  project.
  + apply I_WauthA_iff; auto.
  + apply R_WauthA_iff; auto.
Qed.


(******************************************************)
(** Well-authentication on the real system regarding B *)
(******************************************************)

theorem [real] R_WauthB_iff :
  forall (tau:timestamp),
  (happens(tau) && (tau = B2 || tau = B3)) =>
  (exec@pred(tau) &&
   yA@tau = a &&
   checksign(<tag1,<<input@B,c@B>,<input@B1,rB>>>, ysigmaA@tau,
             vk (skA)) && mac (<tag1,a>, kmacB@B1) = ymacA@tau)
  <=>
  (exec@pred(tau) && A2 < tau
   && fst(output@A2) = fst(input@tau)
   && fst(snd(output@A2)) = fst(snd(input@tau))
   && snd(snd(output@A2)) = snd(snd(input@tau))
   && B1 < A2
   && fst(output@B1) = fst(input@A2)
   && fst(snd(output@B1)) = fst(snd(input@A2))
   && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
   && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
   && A1 < B1 && output@A1 = input@B1
   && B  < B1 && output@B  = input@A1
   && A  < A1 && output@A  = input@B).
Proof.

  intro tau. intro [Hap HB]. split.

  * (** First implication *)
    intro [_ EqB EqSignB EqMacB].
    euf EqSignB.

      intro [H1 H2].
    assert (A2 < tau). {.
      destruct H1 as [H11| H12|H13]. 
      + destruct HB as [HB2 | HB3].
      ++ use depends_B1_B2; constraints.
      ++ use depends_B1_B3; constraints.
      + destruct HB as [HB2 | HB3]. 
      ++ use depends_B_B1; use depends_B1_B2; constraints.
      ++ use depends_B_B1; use depends_B1_B3; constraints.
      + destruct HB as [HB2 | HB3]. 
      ++ use depends_B1_B2; constraints. 
      ++ use depends_B1_B3; constraints.
    }.

    assert exec@A2 as Hexec. apply exec_le (pred tau) A2; constraints.
    assert cond@A2 as HcondA2.  expand exec@A2. constraints.
    rewrite R_WauthA_eq in HcondA2; 1: constraints.
    destruct HcondA2 as [_ HinA2 HinA2' HinA2'' HinA2''' _ HinB1 _ HinA1 _ HinB].
    assert kmacA@A1 = kmacB@tau as EqKey. {
      case HB.
      - rewrite /kmacA /kmacB -HinA1 /output /c.  rewrite !if_true.  
        rewrite -HinB /output /epkA; constraints. 
        rewrite -HinB /output /epkA; constraints.
        rewrite -HinB /output /epkA. 
        rewrite !encap_public_spec encap_shared_spec decap_encap; constraints.
      - rewrite /kmacA /kmacB -HinA1 /output /c. rewrite !if_true.
        rewrite -HinB /output /epkA; constraints.
        rewrite -HinB /output /epkA; constraints.
        rewrite -HinB /output /epkA. 
        rewrite !encap_public_spec encap_shared_spec decap_encap; constraints.
    }.

    apply sufcma in EqSignB.
   (** clear HinA2 HinA2' HinA2''' HinB HinB1. *)
    case HB. 
    -- rewrite HB in *. 
   rewrite /output /ysigmaA /kmacA /kmacB /yA /ymacA in * .
   simpl. constraints.  
    -- rewrite HB in *. 
   rewrite /output /ysigmaA /kmacA /kmacB /yA /ymacA in * .
   simpl. constraints.  

  * (** Second implication *)
   intro [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HinA _ HinB].
   case HB.
   + rewrite HB in *.
     rewrite /output  HinB /sigmaB  /ysigmaA /kmacA  /yA /ymacA /macB /kmacB /xrB /c /epkA /kB in *.
     reduce.
     rewrite -HinB -HinA in *. 
     simpl.
     rewrite decap_encap_public in *. 
     split; congruence.

    + rewrite /output  HinB /sigmaB /ysigmaA /kmacA /yA /ymacA  /macB /kmacB /xrB /c /epkA /kB in *.
      reduce.
      rewrite -HinB  -HinA in *. 
      simpl. 
      rewrite decap_encap_public in *. 
      split; congruence.
Qed.


lemma [real] R_WauthB_eq :
  forall (tau:timestamp),
  happens(tau) && (tau = B2 || tau = B3) => exec@pred(tau) =>
  (yA@tau = a &&
   checksign (<tag1,<<input@B,c@B>,<input@B1,rB>>>, ysigmaA@tau,vk(skA)) &&
   mac (<tag1,a>, kmacB@B1) = ymacA@tau)
  =
  (A2 < tau
   && fst(output@A2) = fst(input@tau)
   && fst(snd(output@A2)) = fst(snd(input@tau))
   && snd(snd(output@A2)) = snd(snd(input@tau))
   && B1 < A2
   && fst(output@B1) = fst(input@A2)
   && fst(snd(output@B1)) = fst(snd(input@A2))
   && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
   && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
   && A1 < B1 && output@A1 = input@B1
   &&  B < B1 && output@B  = input@A1
   &&  A < A1 && output@A  = input@B).
Proof.
  intro tau [_ _] He. rewrite eq_iff.
  have Hw := R_WauthB_iff tau _; 1: constraints. 
  assert exec@(pred tau) = true as Hr. assumption. 
  rewrite Hr // in Hw.
Qed.

(*******************************************************)
(** Well-authentication on the ideal system regarding B *)
(*******************************************************)

lemma [ideal] I_WauthB_iff :
forall (tau:timestamp),
  (happens(tau) && (tau = B2 || tau = B3)) =>
   (exec@pred(tau) && yA@tau =a && checksign (<tag1,<<input@B,c@B>,<input@B1,rB>>>, ysigmaA@tau,
                   vk (skA)) && mac (<tag1,a>, kmacB@B1) = ymacA@tau)
  <=> (exec@pred(tau) && A2 < tau
               && fst(output@A2) = fst(input@tau)
               && fst(snd(output@A2)) = fst(snd(input@tau))
               && snd(snd(output@A2)) = snd(snd(input@tau))
               && B1 < A2
               && fst(output@B1) = fst(input@A2)
               && fst(snd(output@B1)) = fst(snd(input@A2))
               && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
               && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
               && A1 < B1 && output@A1 = input@B1
               && B  < B1 && output@B  = input@A1
               && A < A1 && output@A = input@B
               ).
Proof.
  intro tau [Hap HB]; split.

  * (** First implication *)
    intro [_ EqB EqSignB EqMacB].
    euf EqSignB.
    intro [H1 H2].

    assert (A2 < tau). {
    case H1; case HB.
      + constraints.
      + constraints.
      + use depends_B_B1;   use depends_B1_B2; constraints; constraints.
      + use depends_B_B1;   use depends_B1_B3; constraints; constraints.
      + use depends_B1_B2; constraints; constraints.
      + use depends_B1_B3; constraints; constraints.
    }.
    assert exec@A2 as _. apply exec_le (pred tau) A2; constraints. 
    expand exec@A2.
    assert cond@A2 as HcondA2 by assumption. 
    rewrite I_WauthA_eq in HcondA2; 1: constraints. 
    destruct HcondA2 as [_ HinA2 HinA2' HinA2'' HinA2''' _ HinB1 _ HinA1 _ HinB].

    assert kmacA@A1 = kmacB@B1 as EqKey. {. 
    clear HinA2 HinA2' HinA2'' HinA2'''.
      case HB.
      - rewrite /kmacA /kmacB -HinA1 /output. 
        rewrite /c !if_true. 
          ++ rewrite -HinB /output /epkA; constraints.
          ++ rewrite -HinB /output /epkA; constraints.
          ++ rewrite !if_true -HinB /output /epkA; constraints. 
          ++ rewrite -HinB /output /epkA; constraints.
      - rewrite /kmacA /kmacB -HinA1 /output. 
        rewrite /c !if_true. 
          ++ rewrite -HinB /output /epkA; constraints.
          ++ rewrite -HinB /output /epkA; constraints.
          ++ rewrite !if_true -HinB /output /epkA; constraints. 
          ++ rewrite -HinB /output /epkA; constraints.
    }.

    apply sufcma in EqSignB.
    case HB. 
    -- rewrite HB in *. 
       rewrite /output /ysigmaA /kmacA /kmacB /yA /ymacA in * .
       simpl.  constraints.  
    -- rewrite HB in *. 
       rewrite /output /ysigmaA /kmacA /kmacB /yA /ymacA in * .
       simpl. constraints.  


  * (** Second implication *)
   intro [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 HinA _ HinB].
   case HB.
   + rewrite HB in *.
     rewrite /output HinB /sigmaB /ysigmaA /kmacA /yA /ymacA /macB /kmacB /xrB /c /epkA in *.
     reduce.
     rewrite -HinB -HinA in *. 
     simpl.
     congruence.

    + rewrite /output HinB /sigmaB /ysigmaA /kmacA /yA /ymacA /macB /kmacB /xrB /c /epkA in *.
      reduce.
      rewrite -HinB  -HinA in *. 
      simpl. 
      congruence.
Qed.



lemma [ideal] I_WauthB_eq :
  forall (tau:timestamp),
  happens(tau) && (tau = B2 || tau = B3)  => exec@pred(tau) =>
  (yA@tau = a &&
   checksign (<tag1,<<input@B,c@B>,<input@B1,rB>>>, ysigmaA@tau,vk(skA)) &&
   mac (<tag1,a>, kmacB@B1) = ymacA@tau)
  =
  (A2 < tau
   && fst(output@A2) = fst(input@tau)
   && fst(snd(output@A2)) = fst(snd(input@tau))
   && snd(snd(output@A2)) = snd(snd(input@tau))
   && B1 < A2
   && fst(output@B1) = fst(input@A2)
   && fst(snd(output@B1)) = fst(snd(input@A2))
   && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
   && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
   && A1 < B1 && output@A1 = input@B1
   &&  B < B1 && output@B  = input@A1
   &&  A < A1 && output@A  = input@B).
Proof.
  intro tau [_ _] He. rewrite eq_iff.
  have Hw := I_WauthB_iff tau _; 1: constraints.
  assert exec@(pred tau) = true as Hr by assumption.
  rewrite Hr // in Hw.
Qed.

(** Corollaries of well-authentication for B *)

lemma [real/left,real/right,ideal/left,ideal/right] exec_B2_eq :
  forall (tau:timestamp),
  happens(tau) && (tau = B2) =>
  exec@tau =
  (exec@pred(tau) &&
  (A2 < tau
   && fst(output@A2) = fst(input@tau)
   && fst(snd(output@A2)) = fst(snd(input@tau))
   && snd(snd(output@A2)) = snd(snd(input@tau))
   && B1 < A2
   && fst(output@B1) = fst(input@A2)
   && fst(snd(output@B1)) = fst(snd(input@A2))
   && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
   && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
   && A1 < B1 && output@A1 = input@B1
   &&  B < B1 && output@B  = input@A1
   &&  A < A1 && output@A  = input@B)).
Proof.
  intro tau [_ _].
  project.
  + rewrite /exec /cond.
    rewrite R_WauthB_eq; constraints.
  + rewrite /exec /cond.
    rewrite R_WauthB_eq; constraints.
  + rewrite /exec /cond.
    rewrite I_WauthB_eq; constraints.
  + rewrite /exec /cond.
    rewrite I_WauthB_eq; constraints.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] exec_B3_eq :
  forall (tau:timestamp),
  happens(tau) && (tau = B3) =>
  exec@tau =
  (exec@pred(tau) &&
  not(A2 < tau
   && fst(output@A2) = fst(input@tau)
   && fst(snd(output@A2)) = fst(snd(input@tau))
   && snd(snd(output@A2)) = snd(snd(input@tau))
   && B1 < A2
   && fst(output@B1) = fst(input@A2)
   && fst(snd(output@B1)) = fst(snd(input@A2))
   && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
   && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
   && A1 < B1 && output@A1 = input@B1
   &&  B < B1 && output@B  = input@A1
   &&  A < A1 && output@A  = input@B)).
Proof.
  intro tau [_ _].
  project.
  + rewrite /exec /cond.
    rewrite R_WauthB_eq; constraints.
  + rewrite /exec /cond.
    rewrite R_WauthB_eq; constraints.
  + rewrite /exec /cond.
    rewrite I_WauthB_eq; constraints.
  + rewrite /exec /cond.
    rewrite I_WauthB_eq; constraints.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] exec_B23_eq :
  forall (tau:timestamp),
  happens(tau) && (tau = B2 || tau = B3) =>
  exec@tau =
  (exec@pred(tau) &&
  ((tau = B2) = (A2 < tau
   && fst(output@A2) = fst(input@tau)
   && fst(snd(output@A2)) = fst(snd(input@tau))
   && snd(snd(output@A2)) = snd(snd(input@tau))
   && B1 < A2
   && fst(output@B1) = fst(input@A2)
   && fst(snd(output@B1)) = fst(snd(input@A2))
   && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
   && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
   && A1 < B1 && output@A1 = input@B1
   &&  B < B1 && output@B  = input@A1
   &&  A < A1 && output@A  = input@B))).
Proof.
  intro tau [_ [H1|H2]].
  + project; rewrite H1;
    rewrite exec_B2_eq; [1: constraints]; simpl; constraints.

  + project;
    (assert (tau = B2) = false as -> by constraints);
    simpl; rewrite exec_B3_eq; [1:constraints]; simpl; constraints. 
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] exec_B2_input_B :
  happens(B2) => exec@B2 => input@B = kem_pub eskA.
Proof.
  intro Ha He.
  project.
  +  rewrite exec_B2_eq in He; [1:constraints];  expand output@A; rewrite /epkA in He; constraints.
  +  rewrite exec_B2_eq in He; [1:constraints];  expand output@A; rewrite /epkA in He; constraints.
  +  rewrite exec_B2_eq in He; [1:constraints];  expand output@A; rewrite /epkA in He; constraints.
  +  rewrite exec_B2_eq in He; [1:constraints];  expand output@A; rewrite /epkA in He; constraints.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] exec_B2_add_input_B :
  happens(B2) => exec@B2 = (exec@B2 && input@B = kem_pub eskA).
Proof.
  intro Hap.
  project.
 +  rewrite exec_B2_input_B; [1,2:constraints]. simpl. constraints.
 +  rewrite exec_B2_input_B; [1,2:constraints]. simpl. constraints.
 +  rewrite exec_B2_input_B; [1,2:constraints]. simpl. constraints.
 +  rewrite exec_B2_input_B; [1,2:constraints]. simpl. constraints.
Qed.

lemma [real/left,real/right,ideal/left,ideal/right] exec_B2_input_B1 :
  happens(B2) => exec@B2 => input@B1 = rA.
Proof.
  intro Ha He.
  project. 
  + rewrite exec_B2_eq in He. auto. expand output@A1. constraints. 
  + rewrite exec_B2_eq in He. auto. expand output@A1. constraints.
  + rewrite exec_B2_eq in He. auto. expand output@A1. constraints.
  + rewrite exec_B2_eq in He. auto. expand output@A1. constraints.
Qed.

(** Re-combining well-authentication lemmas *)

lemma [real/left,ideal/left] WauthB_eq_RI :
  forall (tau:timestamp),
  happens(tau) && (tau = B2 || tau = B3)  => exec@pred(tau) =>
  (yA@tau = a &&
   checksign(<tag1,<<input@B,c@B>,<input@B1,rB>>>,
             ysigmaA@tau,vk(skA)) &&
   mac (<tag1,a>, kmacB@B1) = ymacA@tau)
  =
  (A2 < tau
   && fst(output@A2) = fst(input@tau)
   && fst(snd(output@A2)) = fst(snd(input@tau))
   && snd(snd(output@A2)) = snd(snd(input@tau))
   && B1 < A2
   && fst(output@B1) = fst(input@A2)
   && fst(snd(output@B1)) = fst(snd(input@A2))
   && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
   && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
   && A1 < B1 && output@A1 = input@B1
   &&  B < B1 && output@B  = input@A1
   &&  A < A1 && output@A  = input@B).
Proof.
  intro tau H.
  project.
  + apply R_WauthB_eq; constraints.
  + apply I_WauthB_eq; constraints.
Qed.

lemma [ideal/right,real/right] WauthB_eq_IR :
  forall (tau:timestamp),
  happens(tau) && (tau = B2 || tau = B3)  => exec@pred(tau) =>
  (yA@tau = a &&
   checksign (<tag1,<<input@B,c@B>,<input@B1,rB>>>, ysigmaA@tau,vk(skA)) &&
   mac (<tag1,a>, kmacB@B1) = ymacA@tau)
  =
  (A2 < tau
   && fst(output@A2) = fst(input@tau)
   && fst(snd(output@A2)) = fst(snd(input@tau))
   && snd(snd(output@A2)) = snd(snd(input@tau))
   && B1 < A2
   && fst(output@B1) = fst(input@A2)
   && fst(snd(output@B1)) = fst(snd(input@A2))
   && fst(snd(snd(output@B1))) = fst(snd(snd(input@A2)))
   && snd(snd(snd(output@B1))) = snd(snd(snd(input@A2)))
   && A1 < B1 && output@A1 = input@B1
   &&  B < B1 && output@B  = input@A1
   &&  A < A1 && output@A  = input@B).
Proof.
  intro tau H.
  project.
  + apply I_WauthB_eq; constraints.
  + apply R_WauthB_eq; constraints.
Qed.

(** --------------------------------------------------------------------------*)

(** Lemmas for rewriting diff operators *)


(** On the right *)

lemma [ideal/right,real/right] diff_if ['a] (x:bool,y,y',z:'a) :
  diff(if x then y else z, if x then y' else z) =
  if x then diff(y,y') else z.
Proof. project; constraints. Qed.

(** --------------------------------------------------------------------------*)



(***************************************************************)
(** First equivalence: real versus ideal with output of the key *)
(***************************************************************)

global theorem [real/left, ideal/left] real_ideal (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(
        (skA, skB, kem_pub eskA, (*kfresh,*)
         encap_public r (kem_pub eskA),
         diff(encap_shared r (kem_pub eskA), kBh),
         r',rA, rB),
        frame@tau).
Proof.
  intro _.
  induction tau.

  + (** init *)
    expandall.
    rewrite encap_public_spec encap_shared_spec in 0.
    fa 1.
    crypto KEM_CPA_SINGLE.

  + (** A *)
    rewrite /frame /state /transcript /output /exec /cond; fa (_,_,_), !<_,_>.
    rewrite /epkA.    
    rewrite /input. fa 2.  fa(qatt _). { constraints. } apply IH. 

  + (** A1 *)
    rewrite /frame /state /transcript /output /exec /cond; fa (_,_,_), !<_,_>.
    rewrite /input. fa 2. 
    fa(qatt _). {
      repeat split.
      ++ constraints. 
      ++ intro H. use depends_A1_A2; constraints.
      ++ intro H. use depends_A1_A3; [1:constraints]; constraints. }
    apply IH. 

  + (** A2 *)
    rewrite /frame  /state /transcript /output /xrB /kmacA /epkA; 
    fa (_,_,_), !<_,_>.
    
    rewrite !cond_A2_input_A1 /= in 6; [1,2,3,4,5,6:  expand exec@A2;  constraints]. 

    fa (if _ then _), !<_,_>, (sign _), (mac _), !<_,_>.

    rewrite exec_A2_eq in 5;[1,2: constraints].
    deduce 5. 
 
   rewrite decap_encap_public. 
   deduce 9.  

    rewrite /input.
    fa 2. 
    fa(qatt _). {
      repeat split.
      ++ constraints.
      ++ intro H _. use depends_A1_A2; constraints. 
      }.
      apply IH. 

  + (** A3 *)
    rewrite /frame /state /transcript /output; fa (_,_,_), !<_,_>.
    rewrite exec_A3_eq in 5; [1,2: constraints].  deduce 5.
    rewrite /input. fa 2. fa(qatt _).
    { split. constraints. intro H. use depends_A1_A3; constraints. }
    apply IH.

  + (** B *)
    rewrite /frame /state /transcript /exec /cond /output /c //=; fa (_,_,_), !<_,_>.
    rewrite (eq_eq (encap_public r (input@B)) (encap_public r (kem_pub eskA))).
    { intro *; congruence. }.

   fa 6. fa 6. fa 6. fa 8. 
   rewrite /input.

    fa 2. 
    fa(qatt _). {
      repeat split.
      ++ constraints.
      ++ intro H1. use depends_B_B1; constraints.
      ++ intro H1. use depends_B_B2; constraints.
      ++ intro H1 _. use depends_B_B3; constraints.
      }.
      apply IH. 
  

  + (** B1 *)
    rewrite /frame /state /transcript /exec /cond /output /sigmaB /macB /kmacB /c;
      fa (_,_,_), !<_,_>.
    rewrite !(eq_eq (encap_public r (input@B)) (encap_public r (kem_pub eskA)));
       [1,2,3: intro H Eq; rewrite Eq; constraints].    
    fa (if _ then _), !<_,_>.
    deduce.
    fa mac(_,_).
    rewrite -if_app. fa diff(kdf _,_).
    rewrite if_tuple2. fa diff((_,_),_).
    simpl. 
    deduce.
    rewrite /kB.
    rewrite (eq_eq (encap_shared r (input@B)) (encap_shared r (kem_pub eskA))). 
      {  intro Eq; rewrite Eq. constraints. }

    assert(diff(
             if (input@B = kem_pub eskA) then encap_shared r (kem_pub eskA)
             else encap_shared r' (input@B),
             if (input@B = kem_pub eskA) then kBh else encap_shared r' (input@B)) =
           if input@B = kem_pub eskA then 
           diff(encap_shared r (kem_pub eskA), kBh) else encap_shared r' (input@B)).
     project; constraints.

    rewrite H. fa(if _ then _ else _). fa 3. fa 6. fa 1. 
    have Ord := depends_B_B1.
    fa (qatt _). 
    repeat split; try constraints. 
     ++ intro H2. case H2. use depends_B1_B2; constraints. use depends_B_B2; constraints.
     ++ intro H2. case H2. use depends_B1_B3; constraints. use depends_B_B3; constraints.
     ++ intro H2. case H2. use depends_B1_B2; constraints. use depends_B_B2; constraints.
     ++ intro H2. case H2. use depends_B1_B2; constraints. use depends_B_B2; constraints.
     ++ intro H2. case H2. use depends_B1_B2; constraints. use depends_B_B2; constraints.     
     apply IH. 

  + (** B2 *)
    rewrite /frame /state /transcript /output /keyB.
    rewrite !exec_B2_input_B1 // in 1.
    rewrite exec_B2_input_B // in 1. 
    fa (_,_,_), !<_,_>.
    rewrite /kB exec_B2_input_B //=.
    fa if _ then _.
    fa diff(kdf _,_), diff((_,_),_).
    rewrite exec_B2_eq // in 5. deduce 5.
    rewrite /input. fa 2. fa(qatt _). {
    use depends_B_B1. repeat split; try constraints.  use depends_B1_B2; constraints. }
    apply IH.

  + (** B3 *)
    rewrite /frame /state /transcript /output.
    fa (_,_,_), !<_,_>.
    rewrite /exec /cond. 
    rewrite WauthB_eq_RI in 5. constraints. constraints. 
    deduce 5.
    rewrite /input. fa 2. fa(qatt _). {
    use depends_B_B1. repeat split ; try constraints. use depends_B1_B3; constraints. }
    apply IH.
Qed.

(**********************************************************)
(** Second equivalence: strong secrecy on the ideal system *)
(**********************************************************)

global theorem [ideal] strong_sec (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(
        (skA,skB,kem_pub eskA,kfresh,r,r',rA,rB,
         kdf(<tagmac,<kem_pub eskA, encap_public r (kem_pub eskA)>>, kBh)),
        frame@tau).
Proof.
  intro Hap.
  induction tau.

  + (** init *)
    rewrite /frame.  refl.
 
  + (** A *)
    rewrite /frame /state /transcript /exec /cond /output /epkA /input.
    fa (_,_,_); fa !<_,_>. fa 6. fa 2. fa(qatt _).  { constraints. } apply IH.


  + (** A1 *)
    rewrite /frame /state /transcript /exec /cond /output /input.
    fa (_,_,_); fa !<_,_>. fa 6. fa 2. 
    fa(qatt _). { 
       repeat split.
       intro t H. constraints.
       intro H1. use depends_A1_A2; constraints.
       intro H1 H2. use depends_A1_A3; constraints.
     } 
    apply IH.

  + (** A2 *)
    rewrite /frame /state /transcript /output. rewrite /xrB /kmacA /epkA.
    rewrite cond_A2_input_A1 in 1. expand exec@A2; constraints. constraints. 
    rewrite cond_A2_input_A2 in 1. expand exec@A2; constraints. constraints.
    fa (_,_,_), !<_,_>. simpl. deduce 6.
    rewrite /exec /cond I_WauthA_eq in 5. constraints.  deduce 5.
    rewrite /input. fa 2. 
    fa(qatt _). {
     split.
     constraints.
     intro H1 _. use depends_A1_A2; constraints.
    }
    apply IH.

  + (** A3 *)
    rewrite /frame /state /transcript /output; fa (_,_,_), !<_,_>; simpl.
    rewrite /exec /cond I_WauthA_eq in 5. constraints.  deduce 5.
    rewrite /input. fa 2. 
    fa(qatt _). {
     split.
     constraints. 
     intro H1. use depends_A1_A3; constraints.
    }
     apply IH.

   + (** B *)
    expandall. 
    fa (_,_,_); fa !<_,_>. fa 6. fa 6. fa 6. fa 7. fa 8. fa 2. 
    fa(qatt _). {
    repeat split.
    constraints.
    intro H1. use depends_B_B1; constraints.
    intro H1. use depends_B_B2; constraints.
    intro H1 _. use depends_B_B3; constraints.
    intro H1. use depends_B_B2; constraints.
   }
   apply IH.


  + (** B1 *)
    rewrite /frame /state /transcript /exec /cond /output; fa (_,_,_), !<_,_>, (if _ then _), !<_,_>.
    rewrite /sigmaB /c in 7; deduce 7.
    rewrite /macB /kmacB /c.
    fa 7.
    assert
      if (input@B = kem_pub (eskA)) then
        kdf (<tagmac,
             <input@B,
              if (input@B = kem_pub (eskA)) then encap_public (r) (input@B)
              else encap_public (r') (input@B)>>, kBh)
      else
        kdf (<tagmac,
             <input@B,
              if (input@B = kem_pub (eskA)) then encap_public (r) (input@B)
              else encap_public (r') (input@B)>>, encap_shared (r') (input@B))
      =
      if input@B = kem_pub eskA then
        kdf (<tagmac,<kem_pub eskA,encap_public r (kem_pub eskA)>>,
             kBh)
      else
        kdf (<tagmac,<input@B,encap_public r' (input@B)>>,
             encap_shared r' (input@B))
      as -> by case input@B = kem_pub eskA.

    fa 7. fa 7. fa 10. fa 11.  fa 2. expand input@B1.   
    have Ord := depends_B_B1.
    fa(qatt _). { 
    repeat split;  [1,2:constraints  | 3,4: use depends_B_B1; constraints].
    ++ intro [H1 | H2]. use depends_B1_B2; constraints. use depends_B_B1; constraints.
    ++ intro [H1 | H2]. use depends_B1_B2; constraints. use depends_B_B2; constraints.
    ++ intro [H1 | H2]. use depends_B1_B2; constraints. use depends_B_B2; constraints.
    ++ intro [H1 | H2]. use depends_B1_B2; constraints. use depends_B_B2; constraints.
    ++ intro [H1 | H2]. use depends_B1_B3; constraints. use depends_B_B3; constraints.
    ++ intro [H1 | H2]. use depends_B1_B3; constraints. use depends_B_B3; constraints.
    ++ intro [H1 | H2]. use depends_B1_B2; constraints. use depends_B_B2; constraints.
 }
   apply IH. 


  + (** B2 *)
    rewrite /frame /transcript /output /keyB.
    rewrite exec_B2_input_B1 in 1 => //.
    fa (_,_,_), !<_,_>.
    assert B1 < B2. use depends_B1_B2; constraints.
    assert B  < B1. use depends_B_B1; constraints.
    rewrite exec_B2_input_B //= in 6.

    prf 6. {
      use tagke_tagmac_neq as Neq. intro Hexec.
      rewrite exec_B2_add_input_B in Hexec; 1: assumption Hap.
      repeat split; [1,2,3,4,6,7,8: intro *; congruence | 5:   intro  *; constraints]. }. 


    fa (if _ then _).

    rewrite /exec /cond I_WauthB_eq in 5 => //. deduce 5.
    fresh 5. constraints.
    rewrite /input /state. 
    fa 2. fa(qatt _). {
    repeat split.
    ++ constraints.
    ++ intro H1. use depends_B1_B2; constraints.
    ++ intro H1 _. constraints.
    ++ intro H1 _. use depends_B1_B2; constraints.
    }
    apply IH.

  + (** B3 *)
    rewrite /frame /state /transcript /output.
    fa (_,_,_), !<_,_>.
    rewrite /exec /cond I_WauthB_eq in 5. constraints. constraints.  deduce 5.
    rewrite /input. 
    fa 2. fa(qatt _). {
    repeat split; constraints. 
    }
    apply IH.
Qed.

(***********************************************************)
(** Third equivalence: ideal versus real with fresh output *)
(***********************************************************)

global theorem
   [set: real/left, ideal/left; equiv: ideal/right, real/right]
  ideal_real' (tau:timestamp[const])
  :
  [happens(tau)] ->
  equiv(
        (skA,skB,kem_pub eskA,
         r',rA,rB),
        frame@tau).
Proof.
  intro _.
  enrich (skA,skB,kem_pub eskA,r',rA,rB,
          encap_public r (kem_pub eskA),
          diff(kBh, encap_shared r (kem_pub eskA))).
  deduce 1.
  induction tau.

  + (** init *)
    expandall. rewrite encap_shared_spec encap_public_spec.
    sym.
    fa 1.
    crypto KEM_CPA_SINGLE.

  + (** A *)
    rewrite /frame /state /transcript /output /exec /cond; fa (_,_,_), !<_,_>.
    rewrite /epkA.
    rewrite /input. fa 2. fa(qatt _). { constraints. }
    apply IH.

  + (** A1 *)
    rewrite /frame /state /transcript /output; fa (_,_,_), !<_,_>.
    rewrite /input. fa 2. fa(qatt _). {
      repeat split; try constraints.
      ++ intro H1. use depends_A1_A2; constraints.
      ++ intro H1 _. use depends_A1_A3; constraints.
    }.
    apply IH.

  + (** A2 *)
    rewrite /frame /state /transcript /output /xrB /kmacA /epkA; fa (_,_,_), !<_,_>.
    rewrite !cond_A2_input_A1 /= in 6; [1,2,3,4,5,6: expand exec@A2; constraints].
    rewrite !cond_A2_input_A2 /= in 6; [1,2: expand exec@A2; constraints].  
    fa (if _ then _), !<_,_>, (sign _), (mac _), !<_,_>.
    rewrite exec_A2_eq in 5 => //. deduce 5.
    rewrite decap_encap_public.
    rewrite /input. fa 2. fa(qatt _). { repeat split; constraints. }
    apply IH.

  + (** A3 *)
    rewrite /frame /state /transcript /output; fa (_,_,_), !<_,_>; simpl.
    rewrite /exec /cond WauthA_eq_IR in 5 => //. deduce 5.
    rewrite /input. fa 2. fa(qatt _). {repeat split; constraints. }
    apply IH.

  + (** B *)
    rewrite /frame /state /transcript /exec /cond /output /c //=; fa (_,_,_), !<_,_>.
    rewrite !(eq_eq (encap_public r (input@B)) (encap_public r (kem_pub eskA))).
    { intro *; congruence. } .
    rewrite /input. fa 6. fa 6. fa 6.  fa 8. fa 2. fa(qatt _). {
      repeat split; try constraints.
      ++ intro H1. use depends_B_B1; constraints.
      ++ intro H1 _. use depends_B_B2; constraints.
      ++ intro H1 _. use depends_B_B3; constraints.
    }.
    apply IH.

  + (** B1 *)
    rewrite /frame /state /transcript /exec /cond /output /sigmaB /macB /kmacB /c;
      fa (_,_,_), !<_,_>; simpl.
    rewrite !(eq_eq (encap_public r (input@B)) (encap_public r (kem_pub eskA)));
      [1,2,3:intro *; congruence].
    fa if _ then _, !<_,_>.
    fa mac _.
    rewrite -if_app in 8. fa 8.
    rewrite if_tuple2 !if_same. fa 8.
    deduce.
    rewrite diff_if in 3.
    rewrite (eq_eq (encap_shared r (input@B)) (encap_shared r (kem_pub eskA))). intro Eq. congruence.
    deduce 3.
    fa 1. 
    fa (qatt _). {
      repeat split.
      ++ constraints.
      ++ constraints.
      ++ intro H1 _. use depends_B1_B2; constraints.
      ++ intro H1 _. use depends_B1_B3; constraints.
      ++ intro H1 _. use depends_B1_B3; constraints.
   }.
   apply IH.

  + (** B2 *)
    rewrite /frame /transcript /output.
    fa (_,_,_), !<_,_>.
    fa 6.
    fresh 6.
    intro [[H1 _ _] | [H2 _ _]].
    use depends_B1_B2; use depends_B_B1; constraints.
    use depends_B1_B2; constraints.

    rewrite /exec /cond WauthB_eq_IR in 5 => //. deduce 5.
    rewrite /input /state. fa 2. fa(qatt _). {
      repeat split. 
      ++ constraints.
      ++ intro H1. use depends_B1_B2; constraints.
      ++ intro H1 _. use depends_B1_B3; constraints.
      ++ intro H1 _. constraints.
    }.
    apply IH.

  + (** B3 *)
    rewrite /frame /state /transcript /output.
    fa (_,_,_), !<_,_>.
    rewrite /exec /cond. rewrite WauthB_eq_IR in 5 => //.
    deduce 5.
    rewrite /input. fa 2. fa(qatt _). { repeat split; constraints. }
    apply IH.
Qed.


(*************************************)
(** Strong secrecy on the real system *)
(*************************************)

global theorem [set: real/left; equiv: real] SSec_real (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau).
Proof.
  intro Hap.
  trans [ideal/left,ideal/right].
  * (** First equivalence: real versus ideal with output of the key. *)
    by apply real_ideal. 
  * (** Second equivalence: strong secrecy on ideal system.  *)
    by apply strong_sec.
  * (** Third equivalence: ideal versus real with output of a fresh name key. *)
    by apply ideal_real'.
Qed.
