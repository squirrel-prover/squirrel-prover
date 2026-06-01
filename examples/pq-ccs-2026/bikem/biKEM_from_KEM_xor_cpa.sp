(** 
  In this file, we prove that the construction of a biKEM is secure
  as soon as at least one of its constituent KEM is secure.
  We only establish CPA-robustness. We consider the plain XOR construction proved in:

  > KEM Combiners
  > Federico Giacon, Felix Heuer, and Bertram Poettering 
  > https://eprint.iacr.org/2018/024

  We assume that KEM1 is CPA secure.

```
BiEncap_pub (pk1,pk2) = <c1,c2>
BiEncap_shared (pk1, pk2) = ke1 XOR ke2
where (c1, ke1) = Encap1(pk1)
  and (c2, ke2) = Encap2(pk2)
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

(** ## First KEM. We assume CPA security. 

  In this file, we prove that the construction of a biKEM - Xor Combiner - is secure (CPA)
  as soon as at least one of its constituent KEM is secure (CPA).

*)

type kem1_skey[serializable].
type kem1_randomness[serializable].


abstract kem_pub1 : kem1_skey -> message.
abstract encap1_public : kem1_randomness -> message -> message.
abstract encap1_shared : kem1_randomness -> message -> message.
abstract decap1 : message -> kem1_skey -> message.

exact axiom [any] KEM1_sound (r:kem1_randomness,k:kem1_skey) :
  decap1 (encap1_public r (kem_pub1 k)) k = (encap1_shared r (kem_pub1 k)).
hint rewrite KEM1_sound.

(** CPA game for KEMs as in, e.g.,
    <https://eprint.iacr.org/2020/1364.pdf> or <https://eprint.iacr.org/2018/903.pdf>.
    This corresponds to the strong secrecy of the shared secret
    `encap r (kem_pub skey) # 1` even when the public encapsulation is revealed. *)
game KEM1_CPA_SINGLE = {
  rnd skey : kem1_skey;
  rnd r : kem1_randomness;
  rnd s : message;

  oracle o_pub = {
    return (kem_pub1 skey)
  }
  oracle o_encap_pub = {
    return (encap1_public r (kem_pub1 skey))
}
  oracle o_encap_shared = {
    return diff(encap1_shared r (kem_pub1 skey), s)
  }
}.


(** -------------------------------------------------------- *)

(** ## Second KEM

    We only assume basic functionality. *)

type kem2_skey[serializable].
type kem2_randomness[serializable].

abstract kem_pub2 : kem2_skey -> message.
abstract encap2_public : kem2_randomness -> message -> message.
abstract encap2_shared : kem2_randomness -> message -> message.
abstract decap2 : message -> kem2_skey -> message.

exact axiom [any] KEM2_sound (r:_,k:_) :
  decap2 (encap2_public r (kem_pub2 k)) k = (encap2_shared r (kem_pub2 k)).
hint rewrite KEM2_sound.

axiom [any] kem2_shared_length (x:kem2_randomness,y:kem2_skey) :
  len (encap2_shared x (kem_pub2 y)) = namelength_message.

(** -------------------------------------------------------- *)

(** ## Bi-KEM interface *)

abstract biencap_public :
  (kem1_randomness * kem2_randomness) -> (message * message) -> message.
axiom [any] biencap_public_spec (x,y:_) :
  biencap_public x y =
  <encap1_public (x # 1) (y # 1),
   encap2_public (x # 2) (y # 2)>.

abstract biencap_shared : (kem1_randomness * kem2_randomness) -> (message * message) -> message.
axiom [any] biencap_shared_spec:
  forall x y, biencap_shared x y =
    (xor (encap1_shared (x # 1) (y # 1))
         (encap2_shared (x # 2) (y # 2))).

abstract bikem_pub : (kem1_skey * kem2_skey) -> (message * message).
axiom [any] bikem_pub_spec:
  forall x, bikem_pub x = (kem_pub1 (x # 1), kem_pub2 (x # 2)).

abstract bidecap : message -> (kem1_skey * kem2_skey) -> message.
axiom [any] bidecap_spec :
  forall x y, bidecap x y = (xor (decap1 (fst x) (y # 1))
                                 (decap2 (snd x) (y # 2))).

lemma [any] biKEM_sound_public :
  forall x y, bidecap (biencap_public x (bikem_pub y)) y = biencap_shared x (bikem_pub y).
Proof.
  by rewrite biencap_public_spec biencap_shared_spec bidecap_spec bikem_pub_spec.
Qed.


(** -------------------------------------------------------- *)

(** ## CPA game for bi-KEM expressed as a protocol *)

(** biKEM keys *)
name sk1: kem1_skey.
name sk2: kem2_skey.

name r1: kem1_randomness.
name r2: kem2_randomness.

(** Randomness that will replace biKEM shared secret. *)
name rand: message.

channel c_pub.
channel c_encap.

process P_pub =
  out(c_pub, format (bikem_pub (sk1,sk2))).

name rand1: message.

process P_encap_middle =
  out(c_encap,
      <biencap_public (r1,r2) (bikem_pub (sk1,sk2)),
       xor rand1 (encap2_shared r2 (kem_pub2 sk2))>).

process P_encap =
  out(c_encap,
      <biencap_public (r1,r2) (bikem_pub (sk1,sk2)),
       diff(biencap_shared (r1,r2) (bikem_pub (sk1,sk2)),
            rand)>).

system [postquantum] real   = Pub: P_pub | Test: P_encap.

system [postquantum] middle = Pub: P_pub | Test: P_encap_middle.


(** -------------------------------------------------------- *)

name nfresh1 : message.

global theorem [set: real/right; equiv: real/left,middle/left]
  StrongSecrecyPart1 (tau:timestamp[const,glob])
:
  [happens(tau)] ->
  equiv(frame@tau,
        (** KEM1 is secure *)
        kem_pub1 sk1,
        encap1_public r1 (kem_pub1 sk1),
        diff(encap1_shared r1 (kem_pub1 sk1), rand1),
        (** KEM2 can be broken *)
        r2, sk2).
Proof.
  intro Hap.
  induction tau.
  + rewrite /frame. 
    fa 0.
    crypto KEM1_CPA_SINGLE (skey:sk1).
  + rewrite /frame /transcript /exec /cond /output /=. 
    rewrite bikem_pub_spec /=. 
    fa 0; fa !<_,_>. 

   (** we open `state` and `input` to see the call to `qatt` *)
   rewrite /state /input. 
   (** we obtain that both projection of `qatt(_)` can be computed from
     `qatt(_)` using `fa` on `1` (careful, it does not worked if called
      on `3`).  *)
   fa 1. 
   (** we move `qatt` inside the top-level quantum distinguisher using `fa` *)
   fa (qatt _). {
     (** This creates a (simple) proof obligation, where we must show
        that we did not used the quantum randomness `qrnd (pred Pub)`
        elsewhere.
        `auto` trivial close this goal. *)
     constraints.
   }.
   (** Now that we dealt with `qatt`, we can conclude using the
      classical deduction technique built-in `apply`. *)
   apply IH.

  + rewrite /frame /transcript /exec /cond /output /=. 
    rewrite biencap_shared_spec biencap_public_spec !bikem_pub_spec /=.
    fa 0; fa !<_,_>.  
    rewrite /state /input. 
    fa 1. 
    fa (qatt _). {constraints. }
    apply IH.
Qed.

global theorem [set: real/right; equiv: real/right,middle/left]
  StrongSecrecyPart2 (tau:timestamp[const,glob])
:
  [happens(tau)] ->
  equiv(frame@tau,
    (** KEM1 is secure *)
    kem_pub1 sk1,  
    encap1_public r1 (kem_pub1 sk1),
    (** the resulting key is indistinguishable from a random *)
    diff(rand, xor rand1 (encap2_shared r2 (kem_pub2 sk2))), 
    (** KEM2 can be broken *)
    r2,sk2).
Proof.
  intro Hap.
  induction tau.
  (** Init *)
  + trans ~right @system:(real/right) 3:rand.
    ++ rewrite /frame.  fa 0.
       crypto KEM1_CPA_SINGLE.
    ++ rewrite /frame.  fa 0.
       crypto XOR_SINGLE.    
       rewrite namelength_rand1 kem2_shared_length; constraints.
  (** Pub *)
  + rewrite /frame /transcript /exec /cond /output /=. 
    rewrite bikem_pub_spec /=. 
    fa 0; fa !<_,_>. 
    rewrite /state /input. fa 1. 
    fa (qatt _). {constraints. }
    apply IH.
  (** Test *)
  + rewrite /frame /transcript /exec /cond /output /=. 
    rewrite biencap_public_spec bikem_pub_spec /=.
    fa 0; fa !<_,_>. 
    rewrite /state /input. fa 1. 
    fa (qatt _). {constraints. }
    apply IH.
Qed.

global theorem [set: real/right; equiv: real] StrongSecrecy(tau:timestamp[const]):
[happens(tau)] -> equiv(frame@tau).
Proof.
 intro Hap.
  trans [middle/left, middle/left].
  * apply StrongSecrecyPart1; [1:constraints].
  * refl. 
  * apply StrongSecrecyPart2; [1:constraints].
Qed.
