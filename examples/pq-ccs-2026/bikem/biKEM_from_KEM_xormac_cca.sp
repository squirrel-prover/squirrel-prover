(** 
   In this file, we prove that the construction is secure
   as soon as at least one of its constituent KEM is secure.
   More precisely, we assume CCA-2 security with a single call to
   the encapsulation oracle for the first KEM, and prove that
   the same game for the bi-KEM is secure. 

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
close Classic.
open Quantum.
set postQuantumEquivs=true.

(** Dummy name to make sure namelength_message is declared. *)
name dummy : message.

(** ------------------------------------------------------------------------ *)

(** ## First KEM

    We assume CCA security. *)

type kem1_skey[serializable].
type kem1_randomness[serializable,large].

abstract kem1_pub : kem1_skey -> message.
abstract encap1_public : kem1_randomness -> message -> message

(** The shared has two parts:
    - part1 for key encapsulation (after a XOR);
    - part2 for the MAC. *)

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

(** CCA2 game with a single call to encapsulation oracle,
    and separate oracles for separate parts of the messages. *)
game KEM1_CCA_SINGLE = {
  rnd skey : kem1_skey;
  rnd r: kem1_randomness;
  rnd s1: message;
  rnd s2: message;
  oracle o_pub = {
    return (kem1_pub skey)
  }
  oracle o_encap_pub = {
    return (encap1_public r (kem1_pub skey))
  }
  oracle o_encap_shared_part1 = {
    return diff(encap1_shared_part1 r (kem1_pub skey), s1)
  }
  oracle o_encap_shared_part2 = {
    return diff(encap1_shared_part2 r (kem1_pub skey), s2)
  }
  oracle o_decap_part1 (c : message) = {
    return
      if c <> (encap1_public r (kem1_pub skey)) then decap1_part1 c skey
  }
  oracle o_decap_part2 (c : message) = {
    return
      if c <> (encap1_public r (kem1_pub skey)) then decap1_part2 c skey
  }
}.

(** ------------------------------------------------------------------------ *)

(** ## Second KEM

    No crypto assumption here, but an assumption on lengths to allow information
    hiding through XOR. *)

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

(** ------------------------------------------------------------------------ *)

(** ## Bi-KEM interface

    We assume a dualmac function, which is EUF when considered as a simple MAC function
    using only the first key. *)

abstract dualmac: message -> (message * message) -> message
hash dualmac1.

(** An axiom to give a meaning to dualmac and to be able to apply EUF. *)
axiom [any] ax_dual_mac (m:message, k: message * message):
  dualmac m k = dualmac1(<m,k#2>, k#1).

abstract make_biencap: message * message * message -> message
abstract extract_mac: message -> message
abstract extract_kem1: message -> message
abstract extract_kem2: message -> message

(** Some axioms to extract each component of the public part of the biencap + surjectivity*)
exact axiom [any] biencap_extract_mac (x1, x2, y:_) :
  extract_mac(make_biencap(x1,x2,y)) = y.

exact axiom [any] biencap_extract_kem1 (x1, x2, y:_) :
  extract_kem1(make_biencap(x1,x2,y)) = x1.

exact axiom [any] biencap_extract_kem2 (x1, x2, y:_) :
  extract_kem2(make_biencap(x1,x2,y)) = x2.


hint rewrite  biencap_extract_mac.
hint rewrite biencap_extract_kem1.
hint rewrite  biencap_extract_kem2. 


abstract well_formed: message -> bool
axiom [any] surjectivity:
 forall x, well_formed(x) => make_biencap(extract_kem1 x, extract_kem2 x, extract_mac x) = x.


abstract bikem_pub : (kem1_skey * kem2_skey) -> (message * message).
axiom [any] bikem_pub_spec:
  forall x, bikem_pub x = (kem1_pub (x # 1), kem2_pub (x # 2)).

abstract biencap_shared :
  (kem1_randomness * kem2_randomness) -> (message * message) -> message.
axiom [any] biencap_shared_spec:
  forall x y, biencap_shared x y = 
    (xor (encap1_shared_part1 (x # 1) (y # 1)) (encap2_shared_part1 (x # 2) (y # 2))).

abstract biencap_mac :
  (kem1_randomness * kem2_randomness) -> (message * message) -> (message * message).
axiom [any] biencap_mac_spec:
  forall x y, biencap_mac x y = 
    (encap1_shared_part2 (x # 1) (y # 1), encap2_shared_part2 (x # 2) (y # 2)).

abstract biencap_public :
  (kem1_randomness * kem2_randomness) -> (message * message) -> message.
  axiom [any] biencap_public_spec (x,y:_) :
  biencap_public x y =
  make_biencap(encap1_public (x # 1) (y # 1), encap2_public (x # 2) (y # 2), 
   dualmac 
     (<encap1_public (x # 1) (y # 1), encap2_public (x # 2) (y # 2)>)
     (biencap_mac x y)). 


abstract bidecap : message -> (kem1_skey * kem2_skey) -> message.
axiom [any] bidecap_spec :
  forall x y,
    bidecap x y =
    if extract_mac x =
       dualmac
         (<extract_kem1 x, extract_kem2 x>)
         (decap1_part2 (extract_kem1 x) (y # 1),
          decap2_part2 (extract_kem2 x) (y # 2))
    then
      xor
        (decap1_part1 (extract_kem1 x) (y # 1)) 
        (decap2_part1 (extract_kem2 x) (y # 2))
    else empty.

lemma [any] biKEM_sound_public :
  forall x y, bidecap (biencap_public x (bikem_pub y)) y = biencap_shared x (bikem_pub y).
Proof.
  by rewrite biencap_public_spec biencap_shared_spec bidecap_spec biencap_mac_spec bikem_pub_spec.   
Qed.

(** ------------------------------------------------------------------------ *)

(** ## CCA2 game for bi-KEM expressed as a protocol *)

abstract format ['a] : 'a -> message.

(** KEM keys *)
name sk1: kem1_skey.
name sk2: kem2_skey.

(** Randomness for encapsulation *)
name r1: kem1_randomness.
name r2: kem2_randomness.

(** Idealizations for KEM1 shared data, parts 1 and 2,
   and for bi-KEM shared data *)
name rand: message.
name rand1: message.
name rand2: message.

channel c_pub.
channel c_encap.
channel c_decap.

process P_pub =
  out(c_pub, format (kem1_pub sk1, kem2_pub sk2)).

process P_encap = 
  out(c_encap,
      <biencap_public (r1,r2) (bikem_pub (sk1,sk2)),
       diff(biencap_shared (r1,r2) (bikem_pub (sk1,sk2)), rand)>).

process P_decap = 
 in(c_decap, x);
  if well_formed(x) && x <> biencap_public (r1,r2) (bikem_pub (sk1,sk2))
     && 
     (extract_mac x) =
      (dualmac
        (<(extract_kem1 x), (extract_kem2 x)>)
        (decap1_part2 (extract_kem1 x) sk1,
         decap2_part2 (extract_kem2 x) sk2))
  then
    out(c_decap,   
        xor
          (decap1_part1 (extract_kem1 x) sk1)
          (decap2_part1 (extract_kem2 x) sk2)).

system [postquantum] CCA = (Pub: P_pub | Encap: P_encap | Decap: !_i P_decap). 

(** We prove observational equivalence for this game by transitivity:
    CCA/left ~ Game01L/left   // rewriting
             ~ Game01L/right  // crypto KEM
             ~ Game12L/left   // crypto EMPTY
             ~ Game12L/right  // XOR
             ~ Game23L/left   // rewriting
             ~ Game23L/right  // EUF            
             ~ Game23R/right  // rewriting
             ~ Game23R/left   // EUF
             ~ Game01R/right  // rewriting
             ~ Game01R/left   // crypto KEM
                             ~ CCA/right   // rewriting *)

(** ------------------------------------------------------------------------ *)

(** Utilities *)

lemma [any] not_iff (phi,psi:bool) :
  (not phi <=> not psi) <=> (phi <=> psi).
Proof.
  case phi; case psi; auto.  
Qed.

game EMPTY = {}.

lemma [any] decap1p1_rewrite ['a] (x:message,f:message->'a) :
  f (decap1_part1 x sk1) =
  if x <> encap1_public r1 (kem1_pub sk1) then
    f (decap1_part1 x sk1)
  else
    f (encap1_shared_part1 r1 (kem1_pub sk1)).
Proof.
  case (x <> encap1_public r1 (kem1_pub sk1)).
  + auto.
  + intro H. rewrite H.  auto.
Qed.

(** ------------------------------------------------------------------------ *)

(** ### Game 0 vs Game 1

    Game 0 is the CCA game modulo trivial rewriting according to `ax_dual_mac`
    (to switch from `dualmac` to `dualmac1`) and `decap1pX_rewrite` (to avoid
    decapsulations that would prevent the application of KEM1's CCA2 game.
    This is shown in `equiv_CCA_0L` and `equiv_CCA_0R` below.

    Game 1 is obtained from Game 0, by replacing
    `encap1_shared_partX rX (kem1_pub sk1)` by `randX` for `X=1` and `2`.
    Equivalence between Game 0 and Game 1 is a consequence of KEM1's CCA2
    security, as shown in `equiv_01L` and `equiv_01R` below. *)

(** Left parts of the games *)

process P_encap01L =
  out(c_encap,
      <(** biencap_public (r1,r2) (bikem_pub (sk1,sk2)) *)
       make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
        dualmac1
          (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
           encap2_shared_part2 r2 (kem2_pub sk2)>,
           diff(encap1_shared_part2 r1 (kem1_pub sk1),rand2))),
       (** biencap_shared (r1,r2) (bikem_pub (sk1,sk2)) *)
       xor
         diff(encap1_shared_part1 r1 (kem1_pub sk1),rand1)
         (encap2_shared_part1 r2 (kem2_pub sk2))>).

process P_decap01L =
  in(c_decap, x);
  if well_formed(x) && x <>
     make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac1
        (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
          encap2_shared_part2 r2 (kem2_pub sk2)>,
         diff(encap1_shared_part2 r1 (kem1_pub sk1), rand2)))
     &&
     if (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1) then
       ((extract_mac x) =
        dualmac1
          (<<(extract_kem1 x), (extract_kem2 x)>, decap2_part2 (extract_kem2 x) sk2>,
	   decap1_part2 (extract_kem1 x) sk1))
     else
       ((extract_mac x) =
        dualmac1
          (<<(extract_kem1 x), (extract_kem2 x)>, decap2_part2 (extract_kem2 x) sk2>,
           diff(encap1_shared_part2 r1 (kem1_pub sk1), rand2)))
  then
    out(c_decap,   
        xor
          (if (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1) then
	     decap1_part1 (extract_kem1 x) sk1
	   else
	     diff(encap1_shared_part1 r1 (kem1_pub sk1), rand1))
          (decap2_part1 (extract_kem2 x) sk2)).

system [postquantum] game01L =
  (Pub: P_pub | Encap: P_encap01L | Decap: !_i P_decap01L).


lemma [CCA/left,game01L/left] cond_decap_CCA_0L (i:index) :
  happens(Decap(i)) =>
  cond@Decap(i) <=>
  (well_formed(input@Decap(i)) && input@Decap(i) <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac
        (<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>)
        (encap1_shared_part2 r1 (kem1_pub sk1),
         encap2_shared_part2 r2 (kem2_pub sk2)))
   &&
    (extract_mac (input@Decap(i))) =
   dualmac
     (<(extract_kem1 (input@Decap(i))), (extract_kem2 (input@Decap(i)))>)
     (decap1_part2 (extract_kem1 (input@Decap(i))) sk1,
      decap2_part2 (extract_kem2 (input@Decap(i))) sk2)).
Proof. 
intro _.
project.
+ rewrite /cond. by rewrite bikem_pub_spec biencap_public_spec biencap_mac_spec.
+ rewrite /cond. rewrite !ax_dual_mac.
 case ((extract_kem1 (input@Decap(i))) <> encap1_public r1 (kem1_pub sk1)). 
    * intro H; auto.
    * intro H. rewrite H. simpl. constraints.
Qed.

lemma [CCA/left,game01L/left] cond_decap1_CCA_0L (i:index) :
  happens(Decap1(i)) =>
  cond@Decap1(i) <=>
  not
  (well_formed(input@Decap1(i)) && input@Decap1(i) <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac
        (<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>)
        (encap1_shared_part2 r1 (kem1_pub sk1),
         encap2_shared_part2 r2 (kem2_pub sk2)))
   &&
    (extract_mac (input@Decap1(i))) =
   dualmac
     (<(extract_kem1 (input@Decap1(i))), (extract_kem2 (input@Decap1(i)))>)
     (decap1_part2 (extract_kem1 (input@Decap1(i))) sk1,
      decap2_part2 (extract_kem2 (input@Decap1(i))) sk2)).
Proof.
intro _.
project.
+ rewrite /cond. by rewrite bikem_pub_spec biencap_public_spec biencap_mac_spec.
+ rewrite /cond. rewrite !ax_dual_mac.
 case ((extract_kem1 (input@Decap1(i))) <> encap1_public r1 (kem1_pub sk1)). 
    * intro H; auto.
    * intro H. rewrite H. simpl. constraints. 
Qed.

global theorem [set:CCA; equiv:CCA/left,game01L/left] equiv_CCA_0L (tau:timestamp[const]) :
  [happens(tau)] -> equiv(frame@tau, sk1, sk2, r1, r2, rand).
Proof.
intro Hap.
induction tau.
 + rewrite /frame. refl.
 +  expandall. fa 0; fa !<_,_>.  fa 1. fa(qatt _). {constraints. } apply IH. 
 + expandall.  
   rewrite biencap_public_spec bikem_pub_spec biencap_shared_spec biencap_mac_spec.
   rewrite ax_dual_mac. simpl. 
   fa 0; fa !<_,_>.  fa 1. fa(qatt _). {constraints. } apply IH. 
 + rewrite /frame /transcript /exec /output.
    fa (_,_,_), !<_,_>, if _ then _, !(_ && _).
    rewrite cond_decap_CCA_0L //.
    rewrite -(decap1p1_rewrite (extract_kem1  (input@Decap(i))) (fun x => x)) in 5.
    simpl.
    rewrite /input /state.
    fa 1. fa(qatt _). {constraints. } 
    apply IH.
 +  rewrite /frame /transcript /exec /output.
    fa (_,_,_), !<_,_>, if _ then _, !(_ && _).
    rewrite cond_decap1_CCA_0L //.
     rewrite /input /state.
    fa 1. fa(qatt _). {constraints. } 
    apply IH.
Qed.

global theorem [game01L]
  equiv_01L (tau:timestamp[const]) : 
  [happens(tau)] -> equiv(frame@tau). 
Proof.
  intro Hap. crypto KEM1_CCA_SINGLE; [1,2,3: constraints].
Qed.

(** ------------------------------------------------------------------------ *)

(** Right parts of Game 0 and Game 1 described above:
    we essentially replace encapsulations by randoms in `CCA/right`. *)

process P_encap01R =
  out(c_encap,
      <(** biencap_public (r1,r2) (bikem_pub (sk1,sk2)) *)
       make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
        dualmac1
          (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
            encap2_shared_part2 r2 (kem2_pub sk2)>,
           diff(encap1_shared_part2 r1 (kem1_pub sk1), rand2))),
       (** biencap_shared (r1,r2) (bikem_pub (sk1,sk2)) *)
       rand>).

process P_decap01R =
  in(c_decap, x);
  if well_formed(x) && x <>
     make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac1
        (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
          encap2_shared_part2 r2 (kem2_pub sk2)>,
         diff(encap1_shared_part2 r1 (kem1_pub sk1),rand2)))
     &&
     if (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1) then
       ((extract_mac x) =
        dualmac1
          (<<(extract_kem1 x), (extract_kem2 x)>, decap2_part2 (extract_kem2  x) sk2>,
	   decap1_part2 (extract_kem1 x) sk1))
     else
       ((extract_mac x) =
        dualmac1
          (<<(extract_kem1 x),(extract_kem2 x)>, decap2_part2 (extract_kem2  x) sk2>,
	   diff(encap1_shared_part2 r1 (kem1_pub sk1), rand2)))
  then
    out(c_decap,   
        xor
          (if (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1) then
	     decap1_part1 (extract_kem1 x) sk1
	   else
	     diff(encap1_shared_part1 r1 (kem1_pub sk1), rand1))
          (decap2_part1 (extract_kem2 x) sk2)).

system [postquantum] game01R =
  (Pub: P_pub | Encap: P_encap01R | Decap: !_i P_decap01R).


lemma [CCA/right,game01R/left]  cond_decap_CCA_0R (i:index) :
  happens(Decap(i)) =>
  cond@Decap(i) <=>
  (well_formed(input@Decap(i)) && input@Decap(i) <>
     make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac
        (<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>)
        (encap1_shared_part2 r1 (kem1_pub sk1),
         encap2_shared_part2 r2 (kem2_pub sk2)))
   &&
   (extract_mac (input@Decap(i))) =
   dualmac
     (<extract_kem1 (input@Decap(i)), extract_kem2 (input@Decap(i))>)
     (decap1_part2 (extract_kem1 (input@Decap(i))) sk1,
      decap2_part2 (extract_kem2 (input@Decap(i))) sk2)).
Proof. 
intro _.
project.
+ rewrite /cond.  by rewrite bikem_pub_spec biencap_public_spec biencap_mac_spec.
+ rewrite /cond. rewrite !ax_dual_mac.
 case ((extract_kem1 (input@Decap(i))) <> encap1_public r1 (kem1_pub sk1)). 
    * intro H => //.  
    * intro H. simpl. rewrite H. auto.  
Qed.

lemma [CCA/right,game01R/left] cond_decap1_CCA_0R (i:index) :
  happens(Decap1(i)) =>
  cond@Decap1(i) <=>
  not
  (well_formed(input@Decap1(i)) && input@Decap1(i) <>
     make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac
        (<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>)
        (encap1_shared_part2 r1 (kem1_pub sk1),
         encap2_shared_part2 r2 (kem2_pub sk2)))
   &&
   (extract_mac (input@Decap1(i))) =
   dualmac
     (<extract_kem1 (input@Decap1(i)), extract_kem2 (input@Decap1(i))>)
     (decap1_part2 (extract_kem1  (input@Decap1(i))) sk1,
      decap2_part2 (extract_kem2 (input@Decap1(i))) sk2)).
Proof.
intro _.
project.
+ rewrite /cond. by rewrite bikem_pub_spec biencap_public_spec biencap_mac_spec.
+ rewrite /cond. rewrite !ax_dual_mac.
 case ((extract_kem1 (input@Decap1(i))) <> encap1_public r1 (kem1_pub sk1)). 
    * intro H => //.
    * intro H. simpl. rewrite H. auto.  
Qed.



global theorem [set:CCA; equiv:CCA/right,game01R/left] equiv_CCA_0R (tau:timestamp[const]) :
  [happens(tau)] -> equiv(frame@tau, sk1, sk2, r1, r2, rand).
Proof.
  intro Hap. induction tau.
 + rewrite /frame. refl.
 + expandall. fa 0; fa !<_,_>.  fa 1. fa(qatt _). {constraints. } apply IH. 
 + expandall.  
   rewrite biencap_public_spec bikem_pub_spec. simpl. 
   rewrite ax_dual_mac. rewrite biencap_mac_spec.
   simpl. fa 0; fa !<_,_>. fa 1. fa(qatt _). {constraints. } apply IH. 
  + rewrite /frame /transcript /exec /output.
    fa (_,_,_), !<_,_>.
    fa if _ then _, !(_ && _).

   rewrite cond_decap_CCA_0R. constraints. 

    rewrite -(decap1p1_rewrite (extract_kem1  (input@Decap(i))) (fun x => x)) in 5. 
    simpl.
    rewrite /state /input. 
    fa 1. fa(qatt _). {constraints.  }
    apply IH.
  + rewrite /frame /transcript /exec /output /state.
    fa (_,_,_), !<_,_>, if _ then _, !(_ && _).
    rewrite cond_decap1_CCA_0R //.
    fa 1. rewrite /input.  fa(qatt _). {constraints. } 
    apply IH.  
Qed.

global theorem [game01R]
  equiv_01R (tau:timestamp[const,glob]) :
  [happens(tau)] -> equiv(frame@tau). 
Proof.
  intro Hap. crypto KEM1_CCA_SINGLE; [1,2,3: constraints].
Qed.

(** ------------------------------------------------------------------------ *)

(** ### Game 1 vs Game 2

   We introduce `rand`, a fresh random, to idealize biencap_shared.
   This amounts to replacing `rand1` everywhere by
   `rand XOR (encap2_shared_part1 r2 (kem2_pub sk2))`.
   This change is performed only on the left (b=0);
   the right parts (b=1) of Game 2 and Game 1 are the same.

   Equivalence is a consequence of XOR's information hiding property. *)

(** Left parts *)

process P_encap12L =
  out(c_encap, <
      make_biencap(encap1_public r1 (kem1_pub sk1),encap2_public r2 (kem2_pub sk2),
        dualmac1
          (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
           encap2_shared_part2 r2 (kem2_pub sk2)>,
           rand2)),
      diff(xor rand1 (encap2_shared_part1 r2 (kem2_pub sk2)), rand)>).

process P_decap12L =
  in(c_decap, x);
  if well_formed(x) && x <>
     make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac1
        (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
          encap2_shared_part2 r2 (kem2_pub sk2)>,
         rand2))
     &&
     if (extract_kem1  x) <> (encap1_public r1 (kem1_pub sk1)) then
       ((extract_mac x) =
        dualmac1
          (<<(extract_kem1 x), (extract_kem2 x)>, decap2_part2 (extract_kem2 x) sk2>,
           decap1_part2 (extract_kem1 x) sk1))
     else
       ((extract_mac x) =
        dualmac1
          (<<(extract_kem1 x), (extract_kem2 x)>, decap2_part2 (extract_kem2 x) sk2>,
           rand2))
  then
  out(c_decap,
      xor
        (if (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1) then
	   decap1_part1 (extract_kem1  x) sk1
         else
           diff(rand1, xor rand (encap2_shared_part1 r2 (kem2_pub sk2))))
        (decap2_part1 (extract_kem2 x) sk2)).

system [postquantum] game12L =
  (Pub: P_pub | Encap: P_encap12L | Decap: !_i P_decap12L).

global theorem [set:CCA; equiv:game01L/right, game12L/left]
  equiv_11L (tau:timestamp[const]) :
  [happens(tau)] -> equiv(frame@tau).
Proof. intro Hap. crypto EMPTY.
Qed.

lemma [any] eq_eq['a]: forall (x,y:'a), x = y => x=y.
Proof.
intro *; constraints. 
Qed.

global theorem [game12L] 
  equiv_12L (tau:timestamp[const,glob]) :
  [happens(tau)] ->
  equiv(
    frame@tau, sk1, sk2, r1, r2, rand2,
    diff(xor rand1 (encap2_shared_part1 r2 (kem2_pub sk2)), rand)).
Proof.
  intro Hap.
  induction tau.

  (** Init *)
  + 
    xor 6, rand1.
    rewrite namelength_rand1 kem2_shared_length //=.
    fresh 6. {constraints. } rewrite /frame. refl.
 (** Pub *)
  + rewrite /frame /transcript /exec /cond /output /=.
    fa (_,_,_). rewrite /input /state. fa !<_,_>. fa 1. fa(qatt _). {constraints. }
    apply IH.
 (** Encap *)
  + rewrite /frame /transcript /exec /cond /output /=.
    fa (_,_,_). rewrite /input /state. fa !<_,_>. fa 1. fa(qatt _). {constraints. }
    apply IH.
  (** Decap *)
  + rewrite /frame /transcript /exec /cond /output /state. fa (_,_,_). fa !<_,_>. fa 5.
    rewrite (eq_eq (diff(rand1, xor rand (encap2_shared_part1 r2 (kem2_pub sk2))))  
                   (xor (encap2_shared_part1 r2 (kem2_pub sk2)) 
                        diff(xor rand1 (encap2_shared_part1 r2 (kem2_pub sk2)), rand))) in 5.
    intro H. project; simpl; constraints.  
    fa 4.  rewrite /input.  fa 1. fa(qatt _). {constraints. } apply IH. 
 (** Decap1 *)
  + rewrite /frame /transcript /exec /cond /output /=.
    fa (_,_,_).  fa !<_,_>.  fa 4. rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    apply IH.
Qed.


(** ------------------------------------------------------------------------ *)

(** Right parts *)
(** nothing to do *)

(** ------------------------------------------------------------------------ *)

(** ### Game 2 vs Game 3

   Immediately reject in decapsulation oracle if
   `fst (fst input) = encap1_public ...`.
   Equivalence relies on EUF assumption on `dualmac1`. *)

(** Left parts *)

process P_encap23L =
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1),encap2_public r2 (kem2_pub sk2),
        dualmac1
          ((<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
           encap2_shared_part2 r2 (kem2_pub sk2)>), 
          rand2)),
       rand>).

process P_decap23L =
  in(c_decap, x);
  if diff(true, (extract_kem1  x) <> encap1_public r1 (kem1_pub sk1))
     && well_formed(x) && 
     x <>
     make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac1
        ((<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
         encap2_shared_part2 r2 (kem2_pub sk2)>),
         rand2))
     &&
     (** Same as game12L/right but with if moved out a bit,
        so that rand2 appears directly in key position. *)
     if (extract_kem1  x) <> encap1_public r1 (kem1_pub sk1) then
       ((extract_mac x) =
        dualmac1 (<<(extract_kem1 x), (extract_kem2 x)>, decap2_part2 (extract_kem2  x) sk2>,
                  decap1_part2 (extract_kem1 x) sk1))
     else
       ((extract_mac x) =
        dualmac1 (<<(extract_kem1 x),(extract_kem2 x)>, decap2_part2 (extract_kem2  x) sk2>,
                  rand2))
  then
  out(c_decap,   
      xor
        (if (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1) then
           decap1_part1 (extract_kem1  x) sk1
         else 
            xor rand (encap2_shared_part1 r2 (kem2_pub sk2))) 
        (decap2_part1 (extract_kem2 x) sk2)).

system [postquantum] game23L =
  (Pub: P_pub | Encap: P_encap23L | Decap: !_i P_decap23L).


(** Right parts *)

process P_encap23R =
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
        dualmac1
          (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
            encap2_shared_part2 r2 (kem2_pub sk2)>,
           rand2)),
       rand>).

process P_decap23R =
  in(c_decap, x);
  if diff(true, (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1))
     && well_formed(x) && 
     x <>
     make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
      dualmac1
        (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>,
          encap2_shared_part2 r2 (kem2_pub sk2)>,
         rand2))
     &&
     if (extract_kem1 x)  <> encap1_public r1 (kem1_pub sk1) then
       ((extract_mac x) =
        dualmac1
          (<<(extract_kem1 x), (extract_kem2 x)>, decap2_part2 (extract_kem2 x) sk2>,
           decap1_part2 (extract_kem1 x) sk1))
     else
       ((extract_mac x) =
        dualmac1
          (<<(extract_kem1 x),(extract_kem2 x)>, decap2_part2 (extract_kem2  x) sk2>,
           rand2))
  then
    out(c_decap, 
        xor
          (if (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1) then
             decap1_part1 (extract_kem1 x) sk1
           else
             rand1)
          (decap2_part1 (extract_kem2 x) sk2)).

system [postquantum] game23R =
  (Pub: P_pub | Encap: P_encap23R | Decap: !_i P_decap23R).

(** Show that the two versions of left part of Game 2 have the same decapsulation
   condition. The only difference is the moving of the conditional. *)
lemma [game12L/right,game23L/left] game2_cond_decap (i:index,tau:timestamp) :
  happens(tau) => (tau = Decap(i)) =>
  (cond@tau <=>
   (well_formed(input@tau) && input@tau <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
    &&
    if (extract_kem1  (input@tau)) <> (encap1_public r1 (kem1_pub sk1)) then
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau)> , decap2_part2 (extract_kem2  (input@tau)) sk2>,
          decap1_part2 (extract_kem1 (input@tau)) sk1))
    else
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2 (input@tau)) sk2>,
          rand2)))).
Proof.
  project; intro *; rewrite /cond; split; intro _; constraints.
Qed.

(** Same as above but with a negation, for Decap1. *)
lemma [game12L/right,game23L/left] game2_cond_decap1 (i:index,tau:timestamp) :
  happens(tau) => (tau = Decap1(i)) =>
  (cond@tau <=>
   not
   (well_formed(input@tau) && input@tau <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
    && 
        if (extract_kem1 (input@tau)) <> (encap1_public r1 (kem1_pub sk1)) then
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau) >, decap2_part2 (extract_kem2  (input@tau)) sk2>,
          decap1_part2 (extract_kem1 (input@tau)) sk1))
    else  
      (extract_mac  (input@tau) =
       dualmac1
         (<< extract_kem1 (input@tau), extract_kem2 (input@tau) >, decap2_part2 (extract_kem2 (input@tau)) sk2>,
          rand2)))) .
Proof.
    project; intro *; rewrite /cond; split; intro _; constraints.
Qed.

(** Use the previous two lemmas to check that two versions of game2 are indeed the same. *)
global theorem [set:CCA; equiv:game12L/right,game23L/left]
  equiv_22L (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau,sk1,sk2,r1,r2,rand1,rand2,rand).
Proof.
  intro Hap.
  induction tau.
   (** Init *)
  +  rewrite /frame. refl.
   (** Pub *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
   (** Encap *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
   (** Decap *)
  + rewrite /frame /transcript /exec /output.
    rewrite (game2_cond_decap i (Decap(i))) in 0; try constraints. 
    fa (_,_,_); fa !<_,_>. fa 4.
    rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
    apply IH.
  + rewrite /frame /transcript /exec /output /state.
    rewrite (game2_cond_decap1 i (Decap1(i))) in 0; try constraints.
    fa (_,_,_); fa !<_,_>. fa 4.
    rewrite /input.  fa 1; fa(qatt _). {constraints. }
    apply IH.
Qed.

(** Show that Decap conditions in game23L/left and /right are actually the same,
   i.e. the immediate rejection condition does not change anything,
   using EUF. *)
lemma [game23L] game23L_euf (tau:timestamp) :
  happens(tau) => well_formed(input@tau) => 
  input@tau <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
  =>
  extract_mac (input@tau) =
    dualmac1
      (<< extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2  (input@tau)) sk2>,
       rand2)
  =>
  extract_kem1  (input@tau) <> encap1_public r1 (kem1_pub sk1).
Proof.
  intro Hap Hwf Hin Hin2. 
  use surjectivity with input@tau; [2: assumption ]. 
  euf Hin2 => //.
Qed.

(** Same works for game23R. *)
(** In the future, the two lemmas could be merged in a single lemma about a 4-system *)
lemma [game23R] game23R_euf (tau:timestamp) :
  happens(tau) => well_formed(input@tau) =>
  input@tau <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
  =>
  extract_mac (input@tau) =
    dualmac1
      (<<extract_kem1 (input@tau), extract_kem2 (input@tau) >, decap2_part2 (extract_kem2 (input@tau)) sk2>,
       rand2)
  =>
  extract_kem1 (input@tau) <> encap1_public r1 (kem1_pub sk1).
Proof.
  intro Hap Hwf Hin Hin2.
  use surjectivity with input@tau; [2:assumption].
  euf Hin2 => //.
Qed.

lemma [game23L] game23_cond_decap (i:index) :
  happens(Decap(i)) =>
  (cond@Decap(i) <=>
   (well_formed(input@Decap(i)) && input@Decap(i) <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
    &&
    if extract_kem1 (input@Decap(i)) <> (encap1_public r1 (kem1_pub sk1)) then
      (extract_mac (input@Decap(i)) =
       dualmac1
         (< <extract_kem1 (input@Decap(i)), extract_kem2 (input@Decap(i))>, decap2_part2 (extract_kem2 (input@Decap(i))) sk2>,
          decap1_part2 (extract_kem1  (input@Decap(i))) sk1))
    else
      (extract_mac  (input@Decap(i)) =
       dualmac1
         (<< extract_kem1(input@Decap(i)), extract_kem2(input@Decap(i)) >, decap2_part2 (extract_kem2 (input@Decap(i))) sk2>,
          rand2)))).
Proof.
  intro Hap.
  project.
  * rewrite /cond. split; intro H; constraints.
  * split.
    + intro Hc. rewrite /cond in Hc.
      split. constraints. 
      rewrite if_true in Hc; 1: constraints. 
      by case (extract_kem1 (input@Decap(i))) <> encap1_public r1 (kem1_pub sk1). 
    + intro [H1 H2].
      rewrite /cond.
      case (extract_kem1 (input@Decap(i))) <> encap1_public r1 (kem1_pub sk1) => Hcase /=.
      - rewrite if_true in H2; constraints.
      - have Heuf := game23L_euf (Decap i). 
        rewrite if_false in H2; constraints.
Qed.

(** Same as above but for Decap1. *)
lemma [game23L] game23_cond_decap1 (i:index) :
  happens(Decap1(i)) =>
  (cond@Decap1(i) <=>
   not
   (well_formed(input@Decap1(i)) && input@Decap1(i) <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
    &&
    if extract_kem1 (input@Decap1(i)) <> (encap1_public r1 (kem1_pub sk1)) then
      (extract_mac (input@Decap1(i)) =
       dualmac1
         (< < extract_kem1 (input@Decap1(i)), extract_kem2 (input@Decap1(i))>, decap2_part2 (extract_kem2  (input@Decap1(i))) sk2>,
          decap1_part2 (extract_kem1 (input@Decap1(i))) sk1))
    else
      (extract_mac (input@Decap1(i)) =
       dualmac1
         (<< extract_kem1 (input@Decap1(i)), extract_kem2 (input@Decap1(i)) >, decap2_part2 (extract_kem2 (input@Decap1(i))) sk2>,
          rand2)))).
Proof.
  intro Hap.
  project.
  * rewrite /cond. split; intro H; constraints.
  * rewrite /cond. rewrite not_iff.
    split.
    + intro [H1 H2 H3].
      split. constraints.
      rewrite if_true in *; constraints.
    + intro [H1 H2].
      case (extract_kem1 (input@Decap1(i))) <> encap1_public r1 (kem1_pub sk1) => Hcase /=.
      - rewrite if_true in H2; constraints.
      - have Heuf := game23L_euf (Decap1(i)).
        rewrite if_false in H2; constraints.
Qed.

(** Finally prove that left parts of Game 2 and Game 3 are equivalent. *)
global theorem [game23L]
  equiv_23L (tau:timestamp[const,glob]) :
  [happens(tau)] ->
  equiv(frame@tau,sk1,sk2,r1,r2,rand2,rand).
Proof.
  intro Hap.
   induction tau.
   (** Init *)
  +  rewrite /frame. refl.
   (** Pub *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
   (** Encap *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
  + rewrite /frame /transcript /exec /state. fa (_,_,_), !<_,_>, (_ && _), if _ then _.
    rewrite /output.
    rewrite (game23_cond_decap i) in 5 => //.
    rewrite /input. fa 1. fa(qatt _). {constraints. }
    apply IH.  
  + rewrite /frame /transcript /exec /state. fa (_,_,_), !<_,_>, (_ && _), if _ then _.
    rewrite /output.
    rewrite (game23_cond_decap1 i) in 5 => //.
    rewrite /input. fa 1. fa(qatt _). {constraints. }
    apply IH.  
Qed.

(** Proofs for right parts *)

lemma [game01R/right,game23R/left] game2R_cond_decap (i:index,tau:timestamp) :
  happens(tau) => (tau = Decap(i)) =>
  (cond@tau <=>
   (well_formed(input@tau) && input@tau <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
    &&
    if extract_kem1  (input@tau) <> (encap1_public r1 (kem1_pub sk1)) then
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2  (input@tau)) sk2>,
          decap1_part2 (extract_kem1 (input@tau)) sk1))
    else
      (extract_mac  (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2  (input@tau)) sk2>,
          rand2)))).
Proof.
  project; intro *; rewrite /cond; split; constraints.
Qed.

lemma [game01R/right,game23R/left] game2R_cond_decap1 (i:index,tau:timestamp) :
  happens(tau) => (tau = Decap1(i)) =>
  (cond@tau <=>
   not
   (well_formed(input@tau) && input@tau <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
    &&
    if extract_kem1  (input@tau) <> (encap1_public r1 (kem1_pub sk1)) then
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau),extract_kem2 (input@tau) >, decap2_part2 (extract_kem2  (input@tau)) sk2>,
          decap1_part2 ( extract_kem1  (input@tau)) sk1))
    else
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2 (input@tau)) sk2>,
          rand2)))).
Proof.
  project; intro *; rewrite /cond; split; constraints.
Qed.

global theorem [set:CCA;equiv:game01R/right,game23R/left] equiv_22R (tau:timestamp[const]) :
  [happens(tau)] -> equiv(frame@tau,sk1,sk2,r1,r2,rand1,rand2,rand).
Proof.
  intro _. induction tau.
  (** Init *)
  +  rewrite /frame. refl.
   (** Pub *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
   (** Encap *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
  + rewrite /frame /transcript /exec /output /state.
    rewrite (game2R_cond_decap i (Decap(i))) in 0; [1,2: constraints].
    fa (_,_,_); fa !<_,_>.  fa 4. rewrite /input.  fa 1. fa(qatt _). {constraints. } apply IH.
  + rewrite /frame /transcript /exec /output /state.
    rewrite (game2R_cond_decap1 i (Decap1(i))) in 0; [1,2: constraints].
    fa (_,_,_); fa !<_,_>.  fa 4. rewrite /input.  fa 1. fa(qatt _). {constraints. } apply IH.
Qed.

lemma [game23R] game23R_cond_decap (i:index,tau:timestamp) :
  happens(tau) => (tau = Decap(i)) => 
  (cond@tau <=>
   (well_formed(input@tau) && input@tau <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
    &&
    if extract_kem1 (input@tau) <> (encap1_public r1 (kem1_pub sk1)) then
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2 (input@tau)) sk2>,
          decap1_part2 (extract_kem1 (input@tau)) sk1))
    else
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2 (input@tau)) sk2>,
          rand2)))).
Proof.
  project; 1: auto.
  intro Hap Htau. rewrite /cond /=.
  split.
  + intro H; constraints. 
  + intro [H1 H2]. 
    repeat split; try constraints. 
    case (extract_kem1 (input@tau) = encap1_public r1 (kem1_pub sk1)) => Hff.
    - destruct H2 as [H2a H2b]. rewrite if_false in H2b. constraints. 
      have Hyp := game23R_euf (Decap(i)).  
         rewrite Htau in H2b, Hap, H1, H2a. have H := Hyp Hap H1 H2a H2b. auto.
    - rewrite if_true in *; constraints.
Qed.

lemma [game23R] game23R_cond_decap1 (i:index,tau:timestamp) :
  happens(tau) => (tau = Decap1(i)) =>
  (cond@tau <=>
   not
   (well_formed(input@tau) && input@tau <>
    make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2),
     dualmac1
       (<<encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)>, 
         encap2_shared_part2 r2 (kem2_pub sk2)>,
        rand2))
    &&
    if extract_kem1  (input@tau) <> (encap1_public r1 (kem1_pub sk1)) then
      (extract_mac (input@tau) =
       dualmac1
         (<<extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2  (input@tau)) sk2>,
          decap1_part2 (extract_kem1  (input@tau)) sk1))
    else
      (extract_mac (input@tau) =
       dualmac1
         (< <extract_kem1 (input@tau), extract_kem2 (input@tau)>, decap2_part2 (extract_kem2 (input@tau)) sk2>,
          rand2)))).
Proof.
  project; 1: auto.
  intro Hap Htau. rewrite /cond not_iff.
  split; 1: constraints.
  intro [H1 H2].
  repeat split; try constraints.
  case (extract_kem1 (input@tau) = encap1_public r1 (kem1_pub sk1)) => Hff.
  - destruct H2 as [H2a H2b]. rewrite if_false in H2b. constraints.
    have Hyp := game23R_euf (Decap1(i)).
    rewrite Htau in H2b, Hap, H1, H2a. have H := Hyp Hap H1 H2a H2b. auto. 
  - rewrite if_true in *; constraints.
Qed.

global theorem [game23R]
  equiv_23R (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau,sk1,sk2,r1,r2,rand2,rand).
Proof.
  intro Hap.
  induction tau.
  (** Init *)
  +  rewrite /frame. refl.
   (** Pub *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
   (** Encap *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints.  }
      apply IH.
  + rewrite /frame /transcript /exec /state.
    fa (_,_,_), !<_,_>, !(_ && _).
    rewrite /output.
    rewrite (if_true (extract_kem1  (input@Decap(i)) <> encap1_public r1 (kem1_pub sk1))) in 6.
    { intro He Hin11. rewrite /cond in He. destruct He as [_ [_ _ Hm]].
      rewrite if_false // in Hm.
      have _ := game23R_euf (Decap(i)) _ _ _; constraints.
    }.
    rewrite (game23R_cond_decap i (Decap(i))) // in 5.
    rewrite /input. fa 1. fa(qatt _). {constraints. } apply IH.
  + rewrite /frame /transcript /exec /state.
    fa (_,_,_), !<_,_>, !(_ && _), if _ then _.
    rewrite (game23R_cond_decap1 i (Decap1(i))) // in 5.
   rewrite /input. fa 1. fa(qatt _). {constraints. } apply IH.
Qed.

(** ------------------------------------------------------------------------ *)

(** Game 3 is secure, i.e. its two projections are equivalent.
    We leverage the immediate rejection condition to show that the only
    differences between the two projections are in unreachable branches
    of conditionals. *)
global theorem [set:CCA;equiv:game23L/right,game23R/right]
  equiv_3 (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau,sk1,sk2,r1,r2,rand2,rand).
Proof.
  intro Hap.
  induction tau.
 (** Init *)
  +  rewrite /frame. refl.
   (** Pub *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints.  }
      apply IH.
   (** Encap *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
  (** Only Decap remains. *)
  + rewrite /frame /transcript /exec /state.
  fa (_,_,_), !<_,_>, !(_ && _).
  rewrite /output.
  rewrite (if_true (extract_kem1  (input@Decap(i)) <> encap1_public r1 (kem1_pub sk1))) // in 6.
  rewrite /cond /input.  fa 1. fa(qatt _). {constraints. }. apply IH.
   (** Decap1 *)
  +   rewrite /frame /transcript /exec /output. 
      fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
      rewrite /input /state.  fa 1; fa(qatt _). {constraints. }
      apply IH.
Qed.


(** -------------------------------------------------------- *)
(** Putting everything together *)

(** We prove observational equivalence for this game by transitivity:
    CCA/left ~ Game01L/left   // rewriting
             ~ Game01L/right  // crypto KEM
             ~ Game12L/left   // crypto EMPTY
             ~ Game12L/right  // XOR
             ~ Game23L/left   // rewriting
             ~ Game23L/right  // EUF            
             ~ Game23R/right  // rewriting
             ~ Game23R/left   // EUF
             ~ Game01R/right  // rewriting
             ~ Game01R/left   // crypto KEM
                             ~ CCA/right   // rewriting *)


global theorem [set:CCA;equiv:CCA] StrongSecrecy(tau:timestamp[const]):
[happens(tau)] -> equiv(frame@tau).
Proof.
 intro Hap.
  trans [game01L/left, game01L/right].
  * apply  equiv_CCA_0L; assumption.
  * apply equiv_01L; assumption.
  * trans [game12L/left, game12L/right].
      - crypto EMPTY.
      - apply equiv_12L; assumption. 
      - trans [game23L/left, game23L/right].
              + apply equiv_22L; assumption.
              + apply equiv_23L; assumption. 
              + trans [game23R/right,game23R/left].
                    ++  apply equiv_3; assumption.
                    ++  apply equiv_23R; assumption. 
                    ++  trans [game01R/right, game01R/left]. 
                          **  sym. apply equiv_22R; assumption.
                          **  apply equiv_01R; assumption.
                          **  sym. apply equiv_CCA_0R; assumption.  
Qed.
