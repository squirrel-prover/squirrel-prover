(** 
  In this file, we try to prove that the construction of a biKEM is secure
  as soon as at least one of its constituent KEM is secure.
  We only establish CPA-robustness. We consider the construction nested dualPRF from

  > Hybrid Key Encapsulation Mechanisms and Authenticated Key Exchange
  > Nina Bindel, Jacqueline Brendel, Marc Fischlin, Brian Goncalves, and Douglas Stebila 
  > https://eprint.iacr.org/2018/903

  We assume that KEM2 is CCA secure.

```
BiEncap_pub (pk1,pk2) = <c1,c2>
BiEncap_shared (pk1,pk2) = h(<c1,c2>, dualh(hext(0,ke1),ke2))
where (c1, ke1) = Encap1(pk1)
  and (c2, ke2) = Encap2(pk2)
```

*)

include Core.
close Classic.
open Quantum.
set postQuantumEquivs=true.

name dummy: message.

(** ------------------------------------------------------------------------ *)

(** ## First KEM

    No crypto assumption here. *)

type kem1_skey[serializable].
type kem1_randomness[serializable].

abstract kem1_pub : kem1_skey -> message.
abstract encap1_public : kem1_randomness -> message -> message
abstract encap1_shared : kem1_randomness -> message -> message
abstract decap1 : message -> kem1_skey -> message.

exact axiom [any] KEM1_sound (r:kem1_randomness,k:kem1_skey) :
  decap1 (encap1_public r (kem1_pub k)) k = encap1_shared r (kem1_pub k).
hint rewrite KEM1_sound.


(** ------------------------------------------------------------------------ *)

(** ## Second KEM

    We assume CPA security. *)

type kem2_skey[serializable].
type kem2_randomness[serializable].

abstract kem2_pub : kem2_skey -> message.
abstract encap2_public : kem2_randomness -> message -> message
abstract encap2_shared : kem2_randomness -> message -> message
abstract decap2 : message -> kem2_skey -> message.

exact axiom [any] KEM2_sound (r:kem2_randomness,k:kem2_skey) :
  decap2 (encap2_public r (kem2_pub k)) k = (encap2_shared r (kem2_pub k)).
hint rewrite KEM2_sound.



(** CPA game for KEMs as in, e.g.,
    <https://eprint.iacr.org/2020/1364.pdf> or <https://eprint.iacr.org/2018/903.pdf>.
    This corresponds to the strong secrecy of the shared secret
    `encap2_shared r (kem2_pub skey)` even when the public encapsulation is revealed. *)
game KEM2_CPA_SINGLE = {
  rnd skey : kem2_skey;
  rnd r: kem2_randomness;
  rnd s: message;

  oracle o_pub = {
    return (kem2_pub skey)
  }
  oracle o_encap_pub = {
    return (encap2_public r (kem2_pub skey))
  }
  oracle o_encap_shared = {
    return diff(encap2_shared r (kem2_pub skey), s);
  } 
}.

(** ------------------------------------------------------------------------ *)

(** ## Bi-KEM interface

    We assume a dualprf function, which is EUF when considered as a simple prf function
    using only the first key. *)

hash h.
hash hext.

abstract const0: message.
abstract dualprf: (message * message) -> message
hash dualprf2.

(** An axiom to give a meaning to dualprf and to be able to apply EUF. *)
axiom [any] ax_dual_prf (k: message  * message):
  dualprf k = dualprf2(k#1, k#2).

abstract make_biencap: message * message -> message
abstract extract_kem1: message -> message
abstract extract_kem2: message -> message

(** Some axioms to extract each component of the public part of the biencap + surjectivity *)
exact axiom [any] biencap_extract_kem1 (x1, x2:_) :
  extract_kem1(make_biencap(x1,x2)) = x1.

exact axiom [any] biencap_extract_kem2 (x1, x2:_) :
  extract_kem2(make_biencap(x1,x2)) = x2.

hint rewrite biencap_extract_kem1.
hint rewrite biencap_extract_kem2. 


abstract well_formed: message -> bool
axiom [any] surjectivity:
 forall x, well_formed(x) => make_biencap(extract_kem1 x, extract_kem2 x) = x.

abstract bikem_pub : (kem1_skey * kem2_skey) -> (message * message).
axiom [any] bikem_pub_spec:
  forall x, bikem_pub x = (kem1_pub (x # 1), kem2_pub (x # 2)).


abstract biencap_public :
  (kem1_randomness * kem2_randomness) -> (message * message) -> message.
  axiom [any] biencap_public_spec (x,y:_) :
  biencap_public x y =
  make_biencap(encap1_public (x # 1) (y # 1), encap2_public (x # 2) (y # 2)).

abstract biencap_shared :
  (kem1_randomness * kem2_randomness) -> (message * message) -> message.
axiom [any] biencap_shared_spec:
  forall x y, biencap_shared x y = h(
biencap_public x y, 
dualprf(hext(const0,(encap1_shared (x # 1) (y # 1))), (encap2_shared (x # 2) (y # 2)))).


abstract bidecap : message -> (kem1_skey * kem2_skey) -> message.
axiom [any] bidecap_spec :
  forall x y,
    bidecap x y =
          h(x, dualprf((hext(const0,decap1 (extract_kem1 x) (y # 1)),
          decap2 (extract_kem2 x) (y # 2)))).

lemma [any] biKEM_sound_public :
  forall x y, bidecap (biencap_public x (bikem_pub y)) y = biencap_shared x (bikem_pub y).
Proof.
  by rewrite biencap_shared_spec biencap_public_spec bidecap_spec bikem_pub_spec. 
Qed.


(** -------------------------------------------------------- *)

(** ## CPA game for bi-KEM expressed as a protocol *)

(** KEM keys *)
name sk1: kem1_skey.
name sk2: kem2_skey.

(** Randomness for encapsulation *)
name r1: kem1_randomness.
name r2: kem2_randomness.

(** Idealization for the biKEM shared data, and for the KEM1 shared data *)
name rand: message.
name rand2: message.
name rand': message.

channel c_pub.
channel c_encap.

abstract format ['a] : 'a -> message.

process P_pub =
  out(c_pub, format (bikem_pub (sk1,sk2))).

process P_encap =
  out(c_encap,
      <biencap_public (r1,r2) (bikem_pub (sk1,sk2)),
       diff(biencap_shared (r1,r2) (bikem_pub (sk1,sk2)),
            rand)>).

system [postquantum] real = (Pub: P_pub | Encap: P_encap).

process P_encap_middle1 =
  out(c_encap,
      <biencap_public (r1,r2) (bikem_pub (sk1,sk2)),
             h(biencap_public (r1,r2) (bikem_pub (sk1,sk2)), dualprf(hext(const0,encap1_shared r1 (kem1_pub sk1)),rand2))>).

system [postquantum] middle1 = (Pub: P_pub | Encap: P_encap_middle1).

process P_encap_middle2 =
  out(c_encap,
      <biencap_public (r1,r2) (bikem_pub (sk1,sk2)),
                h(biencap_public (r1,r2) (bikem_pub (sk1,sk2)), rand')>).

system [postquantum] middle2 = (Pub: P_pub | Encap: P_encap_middle2).


(** -------------------------------------------------------- *)


global theorem [real/left,middle1/left] StrongSecrecyPart1(tau:timestamp[const,glob]):
[happens(tau)] ->
  equiv(frame@tau,
        kem2_pub sk2,
        encap2_public r2 (kem2_pub sk2),
        diff(encap2_shared r2 (kem2_pub sk2), rand2),
        (** KEM1 can be broken *)
        r1, sk1).
Proof.
  intro Hap.
  induction tau.
  (** Init *)
  + rewrite /frame. fa 0.
    crypto KEM2_CPA_SINGLE. 
  (** Pub *)
  + rewrite /frame /transcript /exec /cond /output /state.  
    fa (_,_,_), !<_,_>. fa (if _ then _).
    rewrite bikem_pub_spec /=. 
    rewrite /input. fa 1. fa(qatt _). {auto. } 
    apply IH.
  (** Test *)
  + rewrite /frame /transcript /exec /cond /output /state. 
    fa (_,_,_), !<_,_>. fa (if _ then _).
    rewrite biencap_shared_spec !biencap_public_spec !bikem_pub_spec /=.
    rewrite /input. fa 1. fa(qatt _). {auto. }
    apply IH.
Qed.


global theorem [middle1/left,middle2/left] StrongSecrecyPart2(tau:timestamp[const,glob]):
[happens(tau)] ->
  equiv(frame@tau, r1, sk1,
        r2, sk2).
Proof.
  intro Hap.
  induction tau.
  (** Init *)
  + rewrite /frame. auto. 
  (** Pub *)
  + rewrite /frame /transcript /exec /cond /output /state.  
    fa (_,_,_), !<_,_>. 
    rewrite /input. fa 1. fa(qatt _). {auto. } 
    apply IH.
  (** Test *)
  + rewrite /frame /transcript /exec /cond /output. fa (_,_,_), !<_,_>. 
    rewrite  !biencap_public_spec !bikem_pub_spec /=. fa 5. fa 5. 
    use ax_dual_prf with (hext(const0,encap1_shared r1 (kem1_pub sk1)),rand2). 
    rewrite H in 5. simpl. 
    fa 5. 
    prf 5.     
    fresh 5. auto.  
    rewrite /input  /state. fa 1. fa(qatt _). {auto. } 
    apply IH.
Qed.


global theorem [set:real; equiv:middle2/left, real/right] StrongSecrecyPart3(tau:timestamp[const,glob]):
[happens(tau)] ->
  equiv(frame@tau, r1, sk1,
        r2, sk2).
Proof.
  intro Hap.
  induction tau.
  (** Init *)
  + rewrite /frame. auto. 
  (** Pub *)
  + rewrite /frame /transcript /exec /cond /output /state.  
    fa (_,_,_), !<_,_>. 
    rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
  (** Test *)
  + rewrite /frame /transcript /exec /cond /output. fa (_,_,_), !<_,_>. 
    rewrite  !biencap_public_spec !bikem_pub_spec /=. fa 5. fa 5. 
    prf 5. fresh 5. auto. 
    rewrite /input /state. fa 1. fa(qatt _). {auto. }
    apply IH.
Qed.



global theorem [set: real/left; equiv: real] StrongSecrecy(tau:timestamp[const]):
[happens(tau)] -> equiv(frame@tau).
Proof.
 intro Hap.
  trans [middle1/left, middle2/left].
  * by apply StrongSecrecyPart1.
  * by apply StrongSecrecyPart2.
  * by apply StrongSecrecyPart3. 
Qed.
