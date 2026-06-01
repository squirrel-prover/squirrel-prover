(** 
   In this file, we prove that the construction is CPA-secure
   as soon as at least one of its constituent KEM is CPA-secure.

   This is the XOR-then-MAC bi-KEM construct from

   > Hybrid Key Encapsulation Mechanisms and Authenticated Key Exchange
   > Nina Bindel, Jacqueline Brendel, Marc Fischlin, Brian Goncalves, and Douglas Stebila 
   > https://eprint.iacr.org/2018/903

```
   BiEncap_pub (pk1,pk2) = <<c1, c2>, mac(<c1,c2>, <kmac1,kmac2>)>
   BiEncap_shared (pk1, pk2) = ke1 XOR ke2
   where (c1, ke1|kmac1) = Encap1(pk1)
     and (c2, ke2|kmac2) = Encap2(pk2)
```
*)

include Core.

game XOR_SINGLE = {
  oracle o_xor(x: message) = {
    rnd n1: message;
    rnd n2: message;
    return if len n1 = len x then diff(n2, xor n1 x)
  }
}.

close Classic.
open Quantum.
set postQuantumEquivs=true.

abstract format ['a] : 'a -> message.
name dummy : message.

type kem1_skey[serializable].
type kem1_randomness[serializable].

abstract kem1_pub : kem1_skey -> message.
abstract encap1_public : kem1_randomness -> message -> message

(** the shared has two parts: one used for key encapsulation and one used for the mac *)

abstract encap1_shared_part1 : kem1_randomness -> message -> message
abstract encap1_shared_part2 : kem1_randomness -> message -> message
abstract decap1_part1 : message -> kem1_skey -> message.
abstract decap1_part2 : message -> kem1_skey -> message.

exact axiom [any] KEM1_sound_part1 (r:kem1_randomness,k:kem1_skey) :
  decap1_part1 (encap1_public r (kem1_pub k)) k = encap1_shared_part1 r (kem1_pub k).
exact axiom [any] KEM1_sound_part2 (r:kem1_randomness,k:kem1_skey) :
  decap1_part2 (encap1_public r (kem1_pub k)) k = encap1_shared_part2 r (kem1_pub k).

hint rewrite KEM1_sound_part1.
hint rewrite KEM1_sound_part2.

(** CPA game for KEMs *)

 
game KEM1_CPA_SINGLE = {
  rnd skey : kem1_skey;
  rnd r: kem1_randomness;
  rnd s1: message;
  rnd s2: message;
  
  oracle o_pub = {
    return (kem1_pub skey)
  }
  
  oracle o_encap_pub  = {
    return  ( encap1_public r (kem1_pub skey))
}

oracle o_encap_shared_part1 = {
    return diff(encap1_shared_part1 r (kem1_pub skey), s1)
}

oracle o_encap_shared_part2 = {
    return diff(encap1_shared_part2 r (kem1_pub skey),s2)
  }
}.


(** ## Second KEM *)
(** We only assume basic functionality *)

type kem2_skey[serializable].
type kem2_randomness[serializable].

abstract kem2_pub : kem2_skey -> message.
abstract encap2_public : kem2_randomness -> message -> message
abstract encap2_shared_part1 : kem2_randomness -> message -> message
abstract encap2_shared_part2 : kem2_randomness -> message -> message
abstract decap2_part1 : message -> kem2_skey -> message.
abstract decap2_part2 : message -> kem2_skey -> message.

exact axiom [any] KEM2_sound_part1 (r:kem2_randomness,k:kem2_skey) :
  decap2_part1 (encap2_public r (kem2_pub k)) k = encap2_shared_part1 r (kem2_pub k).
exact axiom [any] KEM2_sound_part2 (r:kem2_randomness,k:kem2_skey) :
  decap2_part2 (encap2_public r (kem2_pub k)) k = encap2_shared_part2 r (kem2_pub k).

hint rewrite KEM2_sound_part1.
hint rewrite KEM2_sound_part2.

axiom [any] kem2_shared_length (x:kem2_randomness,y:kem2_skey) :
  len (encap2_shared_part1 x (kem2_pub y)) = namelength_message.


(** ## Bi-KEM interface *)

abstract bikem_pub : (kem1_skey * kem2_skey) -> (message * message).
exact axiom [any] bikem_pub_spec:
  forall x, bikem_pub x = (kem1_pub (x # 1), kem2_pub (x # 2)).

hint rewrite bikem_pub_spec.

abstract biencap_shared : (kem1_randomness * kem2_randomness) -> (message * message) -> message.
axiom [any] biencap_shared_spec:
  forall x y, biencap_shared x y = 
    (xor (encap1_shared_part1 (x # 1) (y # 1)) (encap2_shared_part1 (x # 2) (y # 2))).

abstract biencap_mac : (kem1_randomness * kem2_randomness) -> (message * message) -> message.
axiom [any] biencap_mac_spec:
  forall x y, biencap_mac x y = 
    <encap1_shared_part2 (x # 1) (y # 1), encap2_shared_part2 (x # 2) (y # 2)>.

hash hmac.

abstract biencap_public :
  (kem1_randomness * kem2_randomness) -> (message * message) -> message.
  axiom [any] biencap_public_spec (x,y:_) :
  biencap_public x y =
  <<encap1_public (x # 1) (y # 1), encap2_public (x # 2) (y # 2)>, 
   hmac( <encap1_public (x # 1) (y # 1), encap2_public (x # 2) (y # 2)>, (biencap_mac x y))>.

abstract bidecap : message -> (kem1_skey * kem2_skey) -> message.
axiom [any] bidecap_spec :
  forall x y, bidecap x y = if ((snd x) = hmac((fst x), <decap1_part2 (fst (fst x)) (y # 1),
                                                         decap2_part2 (snd (fst x)) (y # 2)>)) 
                            then
                            (xor (decap1_part1 (fst (fst x)) (y # 1)) 
                                 (decap2_part1 (snd (fst x)) (y # 2)))
                            else empty.

lemma [any] biKEM_sound_public :
  forall x y, bidecap (biencap_public x (bikem_pub y)) y = biencap_shared x (bikem_pub y).
Proof.
  by rewrite biencap_public_spec biencap_shared_spec bidecap_spec biencap_mac_spec bikem_pub_spec.
Qed.

(** -------------------------------------------------------- *)
(** ## CPA game for bi-KEM expressed as a protocol *)

(** biKEM keys *)
name sk1: kem1_skey.
name sk2: kem2_skey.

(** Just one CPA challenge for now *)
name r1: kem1_randomness.
name r2: kem2_randomness.

(** Randomness that will replace biKEM shared secret. *)
name rand: message.

channel c_pub.
channel c_encap.


process P_pub =
  out(c_pub, format (bikem_pub (sk1,sk2))).


name rand1: message.
name rand2: message.

(** This process does not contain any diff. *)
(** The aim is write the public part as well as the shared part 
of the biencap assuming that kem1 is idealized, i.e. 
we used rand1 instead of the first part of the shared, and rand2 for the second part *)

process P_encap_middle =
  out(c_encap,
      <<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
   hmac(<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
        <rand2, encap2_shared_part2 r2  (kem2_pub sk2)>)>,
             (xor rand1 (encap2_shared_part1 r2 (kem2_pub sk2)))>).

(** The process is assumed to represent the challenge *)
(** On the right, the bishared is replaced by a random *)

process P_encap =
  out(c_encap,
      <biencap_public (r1,r2) (bikem_pub (sk1,sk2)),
       diff(biencap_shared (r1,r2) (bikem_pub (sk1,sk2)),
            rand)>).

system [postquantum] real   = ( Pub: P_pub | Test: P_encap).

system [postquantum] middle = ( Pub: P_pub | Test: P_encap_middle).


(** -------------------------------------------------------- *)

global theorem [set:real/left;equiv:real/left,middle/left] 
StrongSecrecyPart1(tau:timestamp[const,glob]):
  [happens(tau)] ->
  equiv(frame@tau,
        (** KEM1 is secure *)
        kem1_pub sk1,
        encap1_public r1 (kem1_pub sk1),
        diff(encap1_shared_part1 r1 (kem1_pub sk1), rand1),
        diff(encap1_shared_part2 r1 (kem1_pub sk1), rand2),
        (** KEM2 can be broken *)
        r2, sk2).
Proof.
  intro Hap.
  induction tau.
  + rewrite /frame. 
    fa 0.
    crypto KEM1_CPA_SINGLE (skey: sk1).  
  + rewrite  /frame /transcript /exec /cond /output  /=. 
    fa 0; fa !<_,_>. 
    rewrite /state /input. fa 1. 
    fa (qatt _). {constraints. } 
    apply IH.
  + rewrite  /frame /transcript /exec /cond /output /=. 
    rewrite biencap_shared_spec biencap_public_spec  biencap_mac_spec /=. 
    fa 0; fa !<_,_>. 
    rewrite /state /input. fa 1. 
    fa (qatt _). {constraints. } 
    apply IH.
Qed.
    

global theorem [set:real/left; equiv: real/right,middle/left] 
StrongSecrecyPart2(tau:timestamp[const,glob]):
[happens(tau)] ->
  equiv(frame@tau,
    (** KEM1 is secure *)
    kem1_pub sk1,  
    encap1_public r1 (kem1_pub sk1),
    (** We need to add the diff term below in order to open the hmac and conclude *)
    (** Then because of that, we need to apply the crypto tactic kem to take care of this.  *)
    (** Another option could be to get rid of the mac but for this we need to 
       assume something on the mac *)
    diff(encap1_shared_part2 r1 (kem1_pub sk1),rand2),
    (** the resulting key is indistinguishable from a random *)
    diff(rand,xor rand1 (encap2_shared_part1 r2 (kem2_pub sk2))), 
   (** KEM2 can be broken *)
    r2,sk2).
Proof.
  intro Hap.
  induction tau.
  (** Init *)
  + trans ~right @system:(real/right) 4:rand.
    ++ rewrite /frame.  fa 0.
       crypto KEM1_CPA_SINGLE.
    ++ rewrite /frame.  fa 0.
       crypto XOR_SINGLE.    
       rewrite namelength_rand1 kem2_shared_length; constraints.

  (** Pub *)
  + rewrite /frame /transcript /exec /cond /output /=. 
    fa 0; fa !<_,_>. 
    rewrite /state /input. fa 1. 
    fa (qatt _). {constraints.  } 
    apply IH.
  (** Test *)
  + rewrite  /frame /transcript /exec /cond /output /=. 
    rewrite biencap_public_spec biencap_mac_spec /=. 
    fa 0; fa !<_,_>. 
    rewrite /state /input. fa 1. 
    fa (qatt _). {constraints. } 
    apply IH.
Qed.

global theorem [set:real/left; equiv: real] StrongSecrecy(tau:timestamp[const]):
[happens(tau)] -> equiv(frame@tau).
Proof.
 intro Hap.
  trans [middle/left, middle/left].
  * apply StrongSecrecyPart1; [1:constraints].
  * refl. 
  * apply StrongSecrecyPart2; [1:constraints].
Qed.


