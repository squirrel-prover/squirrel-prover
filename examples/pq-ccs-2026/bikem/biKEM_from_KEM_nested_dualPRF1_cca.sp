(** ## Second KEM. We assume CCA security. 

  In this file, we try to prove that the construction of a biKEM is secure
  as soon as at least one of its constituent KEM is secure.
  We establish CCA-robustness. We consider the construction nested dualPRF from

  > Hybrid Key Encapsulation Mechanisms and Authenticated Key Exchange
  > Nina Bindel, Jacqueline Brendel, Marc Fischlin, Brian Goncalves, and Douglas Stebila 
  > https://eprint.iacr.org/2018/903

  We assume that KEM1 is CCA secure.

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

      We assume CCA security. *)

type kem1_skey[serializable].
type kem1_randomness[serializable].

abstract kem1_pub : kem1_skey -> message.
abstract encap1_public : kem1_randomness -> message -> message
abstract encap1_shared : kem1_randomness -> message -> message
abstract decap1 : message -> kem1_skey -> message.

exact axiom [any] KEM1_sound (r:kem1_randomness,k:kem1_skey) :
  decap1 (encap1_public r (kem1_pub k)) k = encap1_shared r (kem1_pub k).
hint rewrite KEM1_sound.


(** CCA game for KEMs as in, e.g.,
    <https://eprint.iacr.org/2020/1364.pdf> or <https://eprint.iacr.org/2018/903.pdf>.
    This corresponds to the strong secrecy of the shared secret
    `encap1_shared r (kem1_pub skey)` even when the public encapsulation 
    is revealed and the attacker has an access to a decapuslation oracle *)

game KEM1_CCA_SINGLE = {
  rnd skey : kem1_skey;
  rnd r: kem1_randomness;
  rnd s: message;

  oracle o_pub = {
    return (kem1_pub skey)
  }
  oracle o_encap_pub = {
    return (encap1_public r (kem1_pub skey))
  }
  oracle o_encap_shared = {
    return diff(encap1_shared r (kem1_pub skey), s);
  } 
  oracle o_decap (c:message) = {
   return if c <> (encap1_public r (kem1_pub skey)) then decap1 c skey
  }
}.


(** ------------------------------------------------------------------------ *)

(** ## Second KEM

No crypto assumption here. *)
  

type kem2_skey[serializable].
type kem2_randomness[serializable].

abstract kem2_pub : kem2_skey -> message.
abstract encap2_public : kem2_randomness -> message -> message
abstract encap2_shared : kem2_randomness -> message -> message
abstract decap2 : message -> kem2_skey -> message.

exact axiom [any] KEM2_sound (r:kem2_randomness,k:kem2_skey) :
  decap2 (encap2_public r (kem2_pub k)) k = (encap2_shared r (kem2_pub k)).
hint rewrite KEM2_sound.

(** ------------------------------------------------------------------------ *)

(** ## Bi-KEM interface

    We assume a dualprf function, which is EUF when considered as a simple prf function
    using only the first key. *)

hash h.
hash hext.

abstract const0: message.
abstract dualprf: (message * message) -> message
hash dualprf1.

(** An axiom to give a meaning to dualprf and to be able to apply EUF. *)
axiom [any] ax_dual_prf (k: message  * message):
  dualprf k = dualprf1(k#2, k#1).

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

(** ## CCA game for bi-KEM expressed as a protocol *)

(** KEM keys *)
name sk1: kem1_skey.
name sk2: kem2_skey.

(** Randomness for encapsulation *)
name r1: kem1_randomness.
name r2: kem2_randomness.

(** Idealization for the biKEM shared data, and for the KEM1 shared data *)
name rand: message.
name rand1: message.
name rand2: message.
name rand': message.

channel c_pub.
channel c_encap.
channel c_decap.

abstract format ['a] : 'a -> message.

process P_pub =
  out(c_pub, format (bikem_pub (sk1,sk2))).

process P_encap =
  out(c_encap,
      <biencap_public (r1,r2) (bikem_pub (sk1,sk2)),
       diff(biencap_shared (r1,r2) (bikem_pub (sk1,sk2)),
            rand)>).

process P_decap = 
  in(c_decap,x);
  if well_formed(x) && x <> biencap_public (r1,r2) (bikem_pub (sk1,sk2)) then
     out(c_decap, h(make_biencap (extract_kem1 x, extract_kem2 x), 
                    dualprf((hext(const0, decap1 (extract_kem1 x) sk1)), decap2 (extract_kem2 x) sk2))).

system [postquantum] CCA = (Pub: P_pub | Encap: P_encap | Decap: !_i P_decap).

(** ------------------------------------------------------------------------ *)

(** Utilities *)

game EMPTY = {}.

lemma [any] decap1_rewrite ['a] (x:message,f:message->'a) :
  f (decap1 x sk1) =
  if x <> encap1_public r1 (kem1_pub sk1) then
    f (decap1 x sk1)
  else
    f (encap1_shared r1 (kem1_pub sk1)).
Proof.
  case (x <> encap1_public r1 (kem1_pub sk1)).
  + auto.
  + by intro ->.
Qed.


(** ------------------------------------------------------------------------ *)


(** GAME 01: we simply expand the definitions of bikem for the left part, and 
on the right we idealized the shared kem1 with rand1 *)

process P_pub_game01 = 
  out(c_pub, format (kem1_pub sk1, kem2_pub sk2)).

process P_encap_game01 = 
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)),      
h(
make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)),
dualprf(hext(const0, diff(encap1_shared r1 (kem1_pub sk1), rand1)), encap2_shared r2 (kem2_pub sk2)))>).

process P_decap_game01 = 
 in(c_decap, x);
   if well_formed(x) 
      && x <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)) 
   then
       out(c_decap, h(make_biencap(extract_kem1 x, extract_kem2 x), 
                      dualprf(hext(const0,  
        if (extract_kem1 x) <> encap1_public r1 (kem1_pub sk1) 
             then decap1 (extract_kem1 x) sk1 else diff(encap1_shared r1 (kem1_pub sk1),rand1)), 
        decap2 (extract_kem2 x) sk2))).

system [postquantum] Game01 = (Pub: P_pub_game01 | Encap: P_encap_game01 | Decap:  !_i P_decap_game01).



(** CCA/left versus Game 01/left *)

global theorem [set:CCA;equiv:CCA/left,Game01/left]
  equiv_CCA01 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau,sk1,r1,sk2,r2). 
Proof.
  intro Hap.  induction tau.
 + auto.
 + expandall. rewrite  bikem_pub_spec. simpl. 
   fa (_,_,_); fa !<_,_>. fa 1. fa(qatt _). {auto. } apply IH.
 + expandall.  rewrite  biencap_shared_spec  biencap_public_spec bikem_pub_spec.  simpl. 
   fa (_,_,_); fa !<_,_>. fa 1. fa(qatt _). {auto. } apply IH.
 + expandall.  rewrite  biencap_public_spec bikem_pub_spec.  
  use decap1_rewrite with (extract_kem1 (qatt (qrnd (pred(Decap(i))),frame @(pred(Decap(i))))#1)), (fun x:message => x). simpl. 
  fa (_,_,_), !<_,_>. rewrite H in 5.  fa 4.  
  fa 1. fa(qatt _). {auto. }
  apply IH. 
 + expandall. rewrite  biencap_public_spec bikem_pub_spec.  simpl. 
   fa (_,_,_); fa !<_,_>. fa 4. fa 1. fa(qatt _). {auto. } apply IH.
Qed.


(** Equivalence between the two parts of Game01 *)


global theorem [set:Game01;equiv:Game01]
  equiv_Game01 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau).
Proof.
  intro Hap.   crypto KEM1_CCA_SINGLE => //.
Qed.


(** GAME 1/1.5: On the right, we now idealized hext(const0, rand1) by rand2 *)

process P_encap_game115 =
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)),  
     h(make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)),
       dualprf(diff(hext(const0, rand1), rand2),encap2_shared r2 (kem2_pub sk2)))>).

process P_decap_game115 = 
 in(c_decap, x);
    if well_formed(x) 
      && x <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)) 
    then
       out(c_decap, h(make_biencap(extract_kem1 x, extract_kem2 x), dualprf(
                  if extract_kem1 x <> encap1_public r1 (kem1_pub sk1) 
                     then hext(const0, decap1 (extract_kem1 x) sk1) 
                     else diff(hext(const0,rand1), rand2),
decap2 (extract_kem2 x) sk2))).


system [postquantum] Game115 = (Pub: P_pub_game01 | Encap: P_encap_game115 | Decap:  !_i P_decap_game115).


lemma [Game01/right,Game115/left] push_if_above_hext  (b:boolean)  (u,v,w:message) :
diff(hext(const0,if b then u else v),w) = diff(if b then hext(const0,u) else hext(const0,v),w).
Proof.
case b => //. 
Qed.

(** No cryptographic reasonning here *)
global theorem [set:CCA;equiv:Game01/right,Game115/left]
  equiv_Game11 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau,sk1,r1,sk2,r2,rand1). 
Proof.
intro Hap.  induction tau.
 + auto.
 + expandall. fa (_,_,_), !<_,_>. fa 1. fa(qatt _). {auto. } apply IH. 
 + expandall. fa (_,_,_), !<_,_>.  fa 1. fa(qatt _). {auto. } apply IH.
 + rewrite /frame /transcript /exec /cond /output. fa (_,_,_), !<_,_>.  fa 5. 
   rewrite (push_if_above_hext  (extract_kem1 (input@Decap(i)) <>
                    encap1_public r1 (kem1_pub sk1))) in 5. 
   fa 4. 
   rewrite /input /state. fa 1. fa(qatt _). {auto. } 
   apply IH.
 + expandall. fa (_,_,_), !<_,_>. fa 4. fa 1. fa(qatt _). {auto. } apply IH. 
Qed.


global theorem
  [set:Game115;equiv:Game115] 
  equiv_Game115 (tau:timestamp[const,glob]) :   
   [happens(tau)] -> 
  equiv(frame@tau, sk1,r1, sk2,r2,
        diff(hext(const0, rand1),rand2)).
Proof.
  intro  Hap. 
  induction tau.
  + prf 5 => //.
    fresh 5 => //. 
  + expandall.
    fa (_,_,_), !<_,_>. fa 1. fa(qatt _). {auto. } apply IH. 
  + expandall.  fa (_,_,_), !<_,_>. fa 1. fa(qatt _). {auto. } apply IH.
  + expandall. fa (_,_,_), !<_,_>. fa 4. fa 1. fa(qatt _). {auto. }  apply IH.
  + expandall. fa (_,_,_), !<_,_>. fa 4. fa 1. fa(qatt _). {auto. }  apply IH.
Qed.


(** GAME 1.5/2: On the right, we now idealized the dualprf(rand2,shared_kem2)  by rand' *)

process P_encap_game152 = 
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)),  
     h(make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)),
       diff(dualprf(rand2,encap2_shared r2 (kem2_pub sk2)), rand'))>).


process P_decap_game152 = 
 in(c_decap, x);
    if well_formed(x) 
      && x <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)) 
    then
       out(c_decap, h(make_biencap(extract_kem1 x, extract_kem2 x),
                  if extract_kem1 x <> encap1_public r1 (kem1_pub sk1) 
                     then  dualprf(hext(const0,decap1 (extract_kem1 x) sk1),  decap2 (extract_kem2 x) sk2)
   else (
if decap2 ( extract_kem2 x) sk2  = encap2_shared  r2 (kem2_pub sk2)
then diff(dualprf(rand2, encap2_shared r2 (kem2_pub sk2)), rand') (** code mort *)
else dualprf(rand2, decap2 (extract_kem2 x) sk2)
)
)).

system [postquantum] Game152 = (Pub: P_pub_game01 | Encap: P_encap_game152 | Decap:  !_i P_decap_game152).


lemma [Game115/right,Game152/left] push_if_above_dualprf  (b:boolean)  (u,v,w,z:message) :
diff(dualprf(if b then u else v,w),z) = diff(if b then dualprf(u,w) else dualprf(v,w),z).
Proof.
case b => //. 
Qed.



lemma [any] eq_eq['a]: forall (x,y:'a), x = y => x=y.
Proof.
auto.
Qed.

(** No cryptographic reasonning here *)
global theorem [set:CCA;equiv:Game115/right,Game152/left]
  equiv_Game1515 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau,sk1,r1,sk2,r2,rand1,rand2). 
Proof.
  intro Hap.  induction tau.
 + auto.
 + expandall. fa (_,_,_), !<_,_>. fa 1. fa(qatt _). {auto. } apply IH. 
 + expandall. fa (_,_,_), !<_,_>. fa 4. fa 1. fa(qatt _). {auto. }   apply IH.
 + rewrite /frame /transcript /exec /output. fa (_,_,_).  fa !<_,_>. 

fa 5.
rewrite ( push_if_above_dualprf  ((extract_kem1 (input@Decap(i))) <>
                 encap1_public r1 (kem1_pub sk1))) in 5. 
simpl. 

rewrite (eq_eq (
if (decap2 (extract_kem2 (input@Decap(i))) sk2 
              = encap2_shared r2 (kem2_pub sk2)) then
       dualprf (rand2, encap2_shared r2 (kem2_pub sk2))
     else
       dualprf
         (rand2, decap2 (extract_kem2 (input@Decap(i))) sk2))

( dualprf
         (rand2, decap2 (extract_kem2 (input@Decap(i))) sk2)
)) in 5.
case (decap2 (extract_kem2 (input@Decap(i))) sk2 
              = encap2_shared r2 (kem2_pub sk2)) => //.
rewrite /state /cond /input. fa 4.   fa 1. fa(qatt _). {auto. }
apply IH.
+ rewrite /frame /transcript /exec /output. fa (_,_,_).  fa !<_,_>.  fa 4. rewrite /cond. 
  rewrite /input /state. fa 1. fa(qatt _). {auto. } apply IH.
Qed.


global theorem
  [set:Game152;equiv:Game152] 
  equiv_Game152 (tau:timestamp[const,glob]) 
: 
  Let moracle = 
    fun x => if x <> encap2_shared r2 (kem2_pub sk2) then dualprf1(x,rand2) 
  in
  [happens(tau)] -> 
  equiv(frame@tau, sk1,r1, sk2,r2,
        diff(dualprf1(encap2_shared r2 (kem2_pub sk2), rand2),rand'),
        moracle).
Proof.
  intro moracle Hap. 
  induction tau.
  + prf 5 => //.  
    fresh 5 => //. 
  +  rewrite /frame /transcript /exec /output. 
     fa (_,_,_).  fa !<_,_>. rewrite /input /state. fa 1. fa(qatt _). {auto. } 
     apply IH. 
  + rewrite /frame /transcript /exec /output. 
    use ax_dual_prf with (rand2, encap2_shared r2 (kem2_pub sk2)). 
    rewrite H in 0.
    fa (_,_,_); fa !<_,_>. rewrite /input /state. fa 1. fa(qatt _). {auto. } apply IH.
  (** Decap *)
  + rewrite /frame /transcript /output /exec /cond /state. 
    fa (_,_,_), !<_,_>.
use surjectivity with input@Decap(i).
rewrite H in 5 => //.

fa 5. fa 5. fa 5.

 rewrite (eq_eq (dualprf (rand2, decap2 (extract_kem2 (input@Decap(i))) sk2))
                   (if decap2 (extract_kem2 (input@Decap(i))) sk2 <> 
                       encap2_shared r2 (kem2_pub sk2) then
                    dualprf (rand2, decap2 (extract_kem2 (input@Decap(i))) sk2))). {
intro *. simpl. rewrite if_true. auto. auto.
    }.
fa 5. 
use ax_dual_prf with (rand2, decap2 (extract_kem2 (input@Decap(i))) sk2).
rewrite H0 in 6.     simpl.
have -> :
      if (decap2 (extract_kem2 (input@Decap(i))) sk2 <>
           encap2_shared r2 (kem2_pub sk2)) then
         dualprf1 (decap2 (extract_kem2 (input@Decap(i))) sk2, rand2) 
      =
      moracle (decap2 (extract_kem2 (input@Decap(i))) sk2) by auto.
 use ax_dual_prf with (rand2, encap2_shared r2 (kem2_pub sk2)).
rewrite H1 in 5.
simpl.     fa 4. rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
  +   rewrite /frame /transcript /exec /output. 
     fa (_,_,_).  fa !<_,_>. rewrite /input /state /cond. 
     fa 4. fa 5. fa 5. fa 5. fa 1. rewrite /input. fa(qatt _). {auto. }
    apply IH.
Qed.


(** GAME 23: On the right, we now idealized the top level h by rand *)


process P_encap_game23 = 
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)), 
       diff( 
          h(make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)), rand'),
          rand)>).



process P_decap_game23 = 
 in(c_decap, x);
 if well_formed(x) 
    && x <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)) 
       then (
           out(c_decap, h(make_biencap(extract_kem1 x, extract_kem2 x),
                if extract_kem1 x <> encap1_public r1 (kem1_pub sk1) 
                   then  dualprf1(decap2 (extract_kem2 x) sk2, hext(const0,decap1 (extract_kem1 x) sk1))
                   else  (if decap2 (extract_kem2 x) sk2 = encap2_shared r2 (kem2_pub sk2) 
                             then   rand' 
                             else dualprf1(decap2 (extract_kem2 x) sk2, rand2))))).

system [postquantum] Game23 = (Pub: P_pub_game01 | Encap: P_encap_game23 | Decap:  !_i P_decap_game23).

(** No cryptographic reasoning here *)
global theorem [set:CCA;equiv:Game152/right,Game23/left]
  equiv_Game22 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau,sk1,r1,sk2,r2,rand',rand1,rand2). 
Proof.
  intro Hap. 
induction tau. 
+ rewrite /frame. auto.
+ rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
+ rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
+ rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. 
  rewrite (ax_dual_prf  (rand2, decap2 (extract_kem2 (input@Decap(i))) sk2)) in 5.
rewrite ( ax_dual_prf  (hext(const0,decap1 (extract_kem1 (input@Decap(i))) sk1), decap2 (extract_kem2 (input@Decap(i))) sk2)) in 5. simpl.  fa 4. rewrite /input /cond. fa 5. fa 5. rewrite /input. 
fa 1. fa(qatt _). {auto. } apply IH.
+ rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
Qed.



lemma [any] push_if_above_h_simpl (b:boolean) (u,v,w:message):
h(w,if b then u else v) = if b then h(w,u) else h(w,v).
Proof.
case b => //.
Qed.


lemma [any] push_if_above_h_simpl_then_only (b:boolean) (u,w:message):
h(w,if b then u) = if b then h(w,u) else h(w,zero).
Proof.
case b => //.
Qed.


global theorem [set:Game23;equiv:Game23]
  equiv_Game23 (tau:timestamp[const,glob]) : 
 Let moracle = fun x => if x <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)) then h(x,rand') in
  [happens(tau)] -> equiv(frame@tau, sk1,r1, sk2,r2, rand1, rand2, 
   diff(h(make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)), rand'),rand),  
   moracle).
Proof.
  intro moracle  Hap.   induction tau.
+ prf 7 => //. fresh 7 => //.
+ rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
+ rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
+ rewrite /frame /transcript /output /exec /cond /state. fa (_,_,_), !<_,_>. 
use surjectivity with input@Decap(i).
rewrite H in 5 => //.


rewrite (eq_eq (dualprf1 (decap2 (extract_kem2 (input@Decap(i))) sk2, rand2)) 
 (if decap2 (extract_kem2 (input@Decap(i))) sk2 <> encap2_shared r2 (kem2_pub sk2) then
                dualprf1 (decap2 (extract_kem2 (input@Decap(i))) sk2, rand2))).
intro *.
rewrite if_true => //.


 
rewrite (eq_eq (rand') (if input@Decap(i) <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2))   then rand')) in 5.
intro *.
rewrite if_true => //.
fa 5. 

use push_if_above_h_simpl with 
  (extract_kem1 (input@Decap(i)) <> encap1_public r1 (kem1_pub sk1)),  
   dualprf1
          (decap2 (extract_kem2 (input@Decap(i))) sk2,
           hext (const0,  decap1 (extract_kem1 (input@Decap(i))) sk1)), 
 if (decap2 (extract_kem2 (input@Decap(i))) sk2 =
               encap2_shared r2 (kem2_pub sk2)) then
        (if (input@Decap(i) <>
             make_biencap
               (encap1_public r1 (kem1_pub sk1),
                encap2_public r2 (kem2_pub sk2))) then rand')
      else if (decap2 (extract_kem2 (input@Decap(i))) sk2 <>
               encap2_shared r2 (kem2_pub sk2)) then
        dualprf1 (decap2 (extract_kem2 (input@Decap(i))) sk2, rand2).
rewrite H0 in 5. clear H0.
fa 5.

use push_if_above_h_simpl with (decap2 (extract_kem2 (input@Decap(i))) sk2 =
          encap2_shared r2 (kem2_pub sk2)), 
(if (input@Decap(i) <>
             make_biencap
               (encap1_public r1 (kem1_pub sk1),
                encap2_public r2 (kem2_pub sk2))) then rand'),
if (decap2 (extract_kem2 (input@Decap(i))) sk2 <>
               encap2_shared r2 (kem2_pub sk2)) then
        dualprf1 (decap2 (extract_kem2 (input@Decap(i))) sk2, rand2).
rewrite H0 in 5.
clear H0.
fa 5.

use push_if_above_h_simpl_then_only with input@Decap(i) <>
          make_biencap
            (encap1_public r1 (kem1_pub sk1),
             encap2_public r2 (kem2_pub sk2)), rand'.
rewrite H0 in 5.
rewrite (eq_eq (h (input@Decap(i), rand')) (if (input@Decap(i) <>
       make_biencap
         (encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)))
     then h (input@Decap(i), rand'))).
intro *.
rewrite if_true => //.
fa 5. 

have -> :
       if (input@Decap(i) <>
       make_biencap
         (encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)))
     then h (input@Decap(i), rand')
      =
      moracle (input@Decap(i)) by auto.
fa 4. rewrite /input.  fa 1. fa(qatt _). {auto. }
 apply IH.
+ rewrite /frame /transcript /output /exec /cond /state. fa (_,_,_), !<_,_>. 
fa 4. rewrite /input. fa 1. fa(qatt _). {auto. } 
apply IH.
Qed.

(** Game 34 *)
(**  rand' is replaved by  dualprf1(encap2_shared r2 (kem2_pub sk2), rand2) *)


process P_encap_game34 = 
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)), rand>).


process P_decap_game34 = 
 in(c_decap, x);
 if well_formed(x) 
    && x <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)) 
       then (
           out(c_decap, h(make_biencap(extract_kem1 x, extract_kem2 x),
                if extract_kem1 x <> encap1_public r1 (kem1_pub sk1) 
                   then  dualprf1(decap2 (extract_kem2 x) sk2, hext(const0,decap1 (extract_kem1 x) sk1) )
                   else  (if decap2 (extract_kem2 x) sk2 = encap2_shared r2 (kem2_pub sk2)
                             then   diff(rand', dualprf1(encap2_shared r2 (kem2_pub sk2), rand2))
                             else dualprf1(decap2 (extract_kem2 x) sk2, rand2))))).


system [postquantum] Game34 = (Pub: P_pub_game01 | Encap: P_encap_game34 | Decap:  !_i P_decap_game34).

(** No cryptographic reasonning here *)
global theorem [set:CCA;equiv:Game23/right,Game34/left]
  equiv_Game33 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau,sk1,r1,sk2,r2,rand,rand',rand1). 
Proof.
  intro Hap.  crypto EMPTY.
Qed.


(** Equivalence between the two parts of Game34 *)


global theorem
  [set:Game34;equiv:Game34] 
  equiv_Game34 (tau:timestamp[const,glob]) 
: 
  Let moracle = 
    fun x => if x <> encap2_shared r2 (kem2_pub sk2) then dualprf1(x,rand2) 
  in
  [happens(tau)] -> 
  equiv(frame@tau, sk1,r1, sk2,r2,
        diff(rand',dualprf1(encap2_shared r2 (kem2_pub sk2),rand2)),
        moracle,rand).
Proof.
intro moracle Hap.
induction tau.
  + prf 5 => //.  
    fresh 5 => //. 
  + rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
  + rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
  (** Decap *)
 + rewrite /frame /transcript /output /exec /cond /state. 
    fa (_,_,_), !<_,_>. 
    use surjectivity with input@Decap(i).
    rewrite H in 5 => //.
    
    fa 5. fa 5. fa 5.
    rewrite (eq_eq (dualprf1 (decap2 (extract_kem2 (input@Decap(i))) sk2, rand2))
                   (if decap2 (extract_kem2 (input@Decap(i))) sk2 <> 
                       encap2_shared r2 (kem2_pub sk2) then
                    dualprf1 (decap2 (extract_kem2 (input@Decap(i))) sk2, rand2))). {
      by rewrite if_true.
    }.
    fa 5. 
    have -> :
      if (decap2 (extract_kem2 (input@Decap(i))) sk2 <>
           encap2_shared r2 (kem2_pub sk2)) then
         dualprf1 (decap2 (extract_kem2 (input@Decap(i))) sk2, rand2) 
      =
      moracle (decap2 (extract_kem2 (input@Decap(i))) sk2) by auto.
    fa 4. rewrite /input.  fa 1. fa(qatt _). {auto. }. apply IH.
  + rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
Qed.


(** Game445 *)
(** rand2 is replaced by hext(const0,rand1 *)


process P_encap_game445 = 
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)), rand>).

process P_decap_game445 = 
 in(c_decap, x);
 if well_formed(x) 
    && x <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)) 
       then (
           out(c_decap, h(make_biencap(extract_kem1 x, extract_kem2 x),
                if extract_kem1 x <> encap1_public r1 (kem1_pub sk1) 
                   then  dualprf1(decap2 (extract_kem2 x) sk2, hext(const0,decap1 (extract_kem1 x) sk1))
                   else  (if decap2 (extract_kem2 x) sk2 = encap2_shared r2 (kem2_pub sk2)
                             then   dualprf1(encap2_shared r2 (kem2_pub sk2), 
   diff(rand2,hext(const0,rand1)))
                             else dualprf1(decap2 (extract_kem2 x) sk2, diff(rand2,hext(const0,rand1))))))).


system [postquantum] Game445 = (Pub: P_pub_game01 | Encap: P_encap_game445 | Decap:  !_i P_decap_game445).


(** No cryptographic reasonning here *)
global theorem [set:CCA;equiv:Game34/right,Game445/left]
  equiv_Game44 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau,sk1,r1,sk2,r2,rand,rand',rand1,rand2). 
Proof.

  intro Hap. crypto EMPTY.
Qed.


global theorem [set:Game445;equiv:Game445] 
equiv_Game445 (tau:timestamp[const,glob]) :
  [happens(tau)] -> 
  equiv(frame@tau, sk1,r1, sk2,r2,
        diff(rand2,hext(const0,rand1)),rand).

Proof.
intro Hap. induction tau.
  + prf 5. fresh 5 => //. 
  + rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
  + rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
  + rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
  + rewrite /frame /transcript /exec /output /state. fa (_,_,_); fa !<_,_>. fa 4. rewrite /cond. 
  rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
Qed.


(** Game 455 *)
(** rand1 is replaced by encap_shared r1 (kem1_pub sk1) *)


process P_encap_game455 = 
  out(c_encap,
      <make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)), rand>).



process P_decap_game455 = 
 in(c_decap, x);
 if well_formed(x) 
    && x <> make_biencap(encap1_public r1 (kem1_pub sk1), encap2_public r2 (kem2_pub sk2)) 
       then (
           out(c_decap, h(make_biencap(extract_kem1 x, extract_kem2 x),
                if extract_kem1 x <> encap1_public r1 (kem1_pub sk1) 
                   then  dualprf1(decap2 (extract_kem2 x) sk2, hext(const0,decap1 (extract_kem1 x) sk1))
                   else  (if decap2 (extract_kem2 x) sk2 = encap2_shared r2 (kem2_pub sk2)
                             then   dualprf1(encap2_shared r2 (kem2_pub sk2), 
   hext(const0,diff(rand1,encap1_shared r1 (kem1_pub sk1))))
                             else dualprf1(decap2 (extract_kem2 x) sk2, hext(const0,diff(rand1,encap1_shared r1 (kem1_pub sk1)))))))).


system [postquantum] Game455 = (Pub: P_pub_game01 | Encap: P_encap_game455 | Decap:  !_i P_decap_game455).



(** No cryptographic reasonning here *)
global theorem [set:CCA;equiv:Game445/right,Game455/left]
  equiv_Game4545 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau,sk1,r1,sk2,r2,rand,rand',rand1,rand2). 
Proof.

  intro Hap. crypto EMPTY.
Qed.


global theorem [set:Game455;equiv:Game455]
  equiv_Game455 (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau).
Proof.
  intro Hap.  sym. crypto KEM1_CCA_SINGLE => //.
Qed.


global theorem [set: CCA; equiv:Game455/right,CCA/right]
  equiv_Game5CCA (tau:timestamp[const,glob]) : 
  [happens(tau)] -> equiv(frame@tau,sk1,r1,sk2,r2,rand).
Proof.
intro Hap.
 induction tau.
+ auto.
+ rewrite /frame /transcript /exec /output.  
  fa (_,_,_), !<_,_>. rewrite bikem_pub_spec.  simpl.
  rewrite /input /state. fa 1. fa(qatt _). {auto. } apply IH.
+ rewrite /frame /transcript /exec /output.  
   fa (_,_,_), !<_,_>. rewrite bikem_pub_spec biencap_public_spec. simpl. 
   rewrite /input /state. fa 1. fa(qatt _). {auto. }
   apply IH.
+ rewrite /frame /transcript /exec /cond /output /state.  fa (_,_,_), !<_,_>. 
fa 5. 
fa 5.

rewrite biencap_public_spec bikem_pub_spec.
simpl.

rewrite (ax_dual_prf  (hext(const0,(decap1 (extract_kem1 (input@Decap(i))) sk1)), (decap2 (extract_kem2 (input@Decap(i))) sk2))) in 5.
simpl. 

rewrite (eq_eq (dualprf1
         (decap2 (extract_kem2 (input@Decap(i))) sk2,
  hext(const0,encap1_shared r1 (kem1_pub sk1)))) (dualprf1
       (
   decap2 (extract_kem2 (input@Decap(i))) sk2,hext(const0,decap1 (extract_kem1 (input@Decap(i))) sk1)))) in 5.
intro *. simpl.
rewrite H. auto.



rewrite (eq_eq (dualprf1
         (encap2_shared r2 (kem2_pub sk2), hext(const0,encap1_shared r1 (kem1_pub sk1)))) (dualprf1
       (decap2 (extract_kem2 (input@Decap(i))) sk2, hext(const0,decap1 (extract_kem1 (input@Decap(i))) sk1))
        )) in 5.
intro *.  simpl. 
rewrite H. 
rewrite Meq. auto. 
simpl. 
fa 4. rewrite /input. fa 1. fa(qatt _). {auto. } apply IH => //.



+ rewrite /frame /transcript /exec /cond /output /state.  fa (_,_,_), !<_,_>. 
rewrite biencap_public_spec bikem_pub_spec.
simpl. fa 4. rewrite /input. fa 1. fa(qatt _). {auto. } apply IH.
Qed.


(** -------------------------------------------------------- *)
(** Putting everything together *)

global theorem [set: CCA/right; equiv: CCA] StrongSecrecy(tau:timestamp[const]):
[happens(tau)] -> equiv(frame@tau).
Proof.
 intro Hap.
  trans [Game01/left, Game01/right].
  * by apply equiv_CCA01. 
  * by apply equiv_Game01.
  * trans [Game115/left, Game115/right].
      - by apply equiv_Game11. 
      - by apply equiv_Game115.
      - trans [Game152/left, Game152/right].
              + by apply equiv_Game1515. 
              + by apply equiv_Game152.
              + trans [Game23/left,Game23/right].
                    ++  by apply equiv_Game22.
                    ++  by apply equiv_Game23. 
                    ++ trans [Game34/left,Game34/right].
                     +++  by apply equiv_Game33.
                     +++  by apply equiv_Game34.  
                     +++  trans [Game445/left, Game445/right].
                          **  by apply equiv_Game44. 
                          **  by apply equiv_Game445.
                          ** trans [Game455/left,Game455/right].
                              ***  by apply equiv_Game4545.
                              ***  by apply equiv_Game455. 
                              ***  by apply equiv_Game5CCA.
Qed.

