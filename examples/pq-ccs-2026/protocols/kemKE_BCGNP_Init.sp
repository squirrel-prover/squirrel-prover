(*******************************************************************************

Generic 2xKEM - key exchange from Key encapsulation Mechanism (KEM)


[A] Boyd, Colin and Cliff, Yvonne and Nieto, Juan M. Gonzalez and Paterson, Kenneth G.
    One-round key exchange in the standard model.

# On KEMs

The protocol uses KEMs. In the paper, they are id-based, which we abstract here.

The KEMs are usally described with
(ek,dk) <- Keygen(r) returns an encryption key ek and a decryption key ek
(k,ct) <- Encap(r,ek) returns a session key k and its cyphertext ct
k <- Decap(ct,dk) returns k.

We abstract this with, pk, encap and decap function symbols, where:
 * dk is a name, ek = pk(dk);
 * k is a name, ct=encap(k,r,pk(dk));
 * decap(encap(k,r,pk(dk)),dk) = k.

# Protocol description

We consider two parties I (initiator) and R (responder).
One KEM (Pk, Encap, DeCap) and two PRFs, Exct and Expd.
There is a public seed skex for Exct.

Static keys for party X :
- skX

Public keys for party X :
- pkX = pk(skX)


         Initiator            |          Responder
 -----------------------------+---------------------------------
  new kI;                     |
  ctI := Encap(kI,rI,pk(skR)) |
                              |
                         --(I,ctI)->
                              |
                              |  new kR;
                              |  ctR := Encap(kR, rR , pk(skI))
                              |
                         <-(R,ctR)-- 
                              |
  kR := Decap(ctR,dkI)        |  kI := Decap(ctI,dkI)
                              |


Final key derivation:
- kI2 := Exct(kI,skex)
- kR2 := Exct(kR,skex)
- s := (I,ctI,R,ctR)
- KIR := expd(s,kI2) XOR expd(s,kR2)

# Model

We model an unbounded number of agents, each capable of initiating multiple sessions.
The responder is willing to talk to anybody.

We prove the strong secrecy of all the keys as seen by the initiator.
Public keys are revealed. We do not consider dishonest agents.

*******************************************************************************)

include Core.

close Classic.
open Quantum.
set postQuantumEquivs = true.

type kem_skey[serializable].
type kem_randomness[serializable].

abstract kem_pub : kem_skey -> message.
abstract encap_public : kem_randomness -> message -> message.
abstract encap_shared : kem_randomness -> message -> message.
abstract decap : message -> kem_skey -> message.

exact axiom [any] KEM_sound (r:kem_randomness,k:kem_skey) :
  decap (encap_public r (kem_pub k)) k = (encap_shared r (kem_pub k)).
hint rewrite KEM_sound.

(** CPA game for KEMs *)
game KEM_CPA_SINGLE = {
  rnd skey : kem_skey;
  rnd r : kem_randomness;
  rnd s : message;
  let pubk = kem_pub skey;

  oracle o_pub = {
    return pubk
  }
  oracle o_encap_pub = {
    return (encap_public r pubk)
  }
  oracle o_encap_shared = {
    return diff(encap_shared r pubk, s)
  }
}.

(** CPA game for multiple keys. This game is stronger than the previous one *)

game KEM_CPA = {
  rnd skey : kem_skey;
  let pubk = kem_pub skey;

  oracle o_pub = {
    return pubk
  }
  oracle o_encap_shared = {
    rnd r : kem_randomness;
    rnd s : message;
    return (
      encap_public r pubk,
      diff(encap_shared r pubk, s)
    )
  }
}.

game XOR_SINGLE = {
  oracle o_xor(x: message) = {
    rnd n1: message;
    rnd n2: message;
    return if len n1 = len x then diff(xor n1 x, n2)
  }
}. 

hash exct

hash expd

(** public random key for exct *)

name skex : message.

(** long term key of I *)

name skI : index-> kem_skey

(** long term key of R *)
name skR : index->  kem_skey
abstract DskR : index->  kem_skey

(** session randomness of I *)
name kI : index * index * index -> message
name kIfresh : index * index * index -> message
name rI : index * index * index -> kem_randomness

abstract DkI : index * index * index -> message
abstract DrI : index * index * index -> kem_randomness

(** session randomness of R *)
name kR : index * index  -> message
name rR : index * index -> kem_randomness

(** ideal key *)
name idealK : index * index * index -> message

abstract ok:message

channel cI
channel cR
mutable sIR(i,j,k:index) : message =  zero.



set processStrictLetMode = true.

(** Squirrel currently doesn't allow a flexible modelling of the length
   of hashes. The PRF assumption implicitly assumes that hashes are
   of length namelength_message (aka the security parameter eta) which
   we also need to make explicit here. *)
axiom [any] len_expd (x,y:message) : len(expd(x,y)) = namelength_message.

process InitReal(i,j,k:index) =
   let ctI = encap_public (rI(i,j,k)) (kem_pub (skR(j))) in
   out(cI, <kem_pub (skI(i)), ctI>); (** public key is revealed *)
   in(cR,xtR);
   if fst(xtR) = kem_pub (skR(j)) then
     let ctRI = snd(xtR) in
     let kI2 = exct(skex,encap_shared (rI(i,j,k)) (kem_pub (skR(j)))) in
     let kR2 = exct(skex,(decap ctRI (skI(i))) ) in
     let s = <kem_pub (skI(i)),<ctI,<kem_pub(skR(j)),ctRI>>> in
   sIR i j k :=  expd(s,kI2) XOR expd(s,kR2); 
   out(cI, diff(sIR i j k, idealK(i,j,k))).

process InitIdeal(i,j,k:index) =
    let ctI = encap_public  (rI(i,j,k)) (kem_pub (skR(j))) in
    out(cI, <kem_pub(skI(i)),ctI>); 
    in(cR,xtR);
    if fst(xtR) = kem_pub(skR(j)) then
      let ctRI = snd(xtR) in
      let kI2 = exct(skex, kIfresh(i,j,k)) in
      let kR2 =exct(skex,decap ctRI (skI(i))) in
      let s = <kem_pub(skI(i)),<ctI,<kem_pub(skR(j)),ctRI>>> in
    sIR i j k :=  expd(s,kI2) XOR expd(s,kR2); 
    out(cI, diff(sIR i j k, idealK(i,j,k))).


process InitToCompromised(i,j,k:index) = 
   let DctI = encap_public  (DrI(i,j,k)) (kem_pub (DskR(j))) in
   out(cI, <kem_pub(skI(i)), DctI>); 
   (** public key is revealed *)
   in(cR,xtR).
   (** Then the key is computed but never used as we will not express strong secrecy
      when the initator is talking to a dishonest responder, thus we not model this part. *)


process Resp(j,k:index) =
   in(cI, xtI);
   let pkI = fst(xtI) in 
   let ctIR = snd(xtI) in
   let ctR = encap_public  (rR(j,k)) pkI in
   out(cR,<kem_pub(skR(j)),ctR>).

system [postquantum] real =
  out(cI,skex);
  ((!_j !_k R: Resp(j,k)) |
   (!_i !_j !_k I: InitReal(i,j,k)) |
   (!_i !_j !_k IC: InitToCompromised(i,j,k))).

system [postquantum] ideal =
  out(cI,skex);
  ((!_j !_k R: Resp(j,k)) |
   (!_i !_j !_k I: InitIdeal(i,j,k)) |
   (!_i !_j !_k IC: InitToCompromised(i,j,k))).



(** Technical lemmas. *)

lemma [real/left,real/left] diff_eq ['a] (x:'a) : diff(x,x) = x.
Proof. by project. Qed.

axiom [any] gt_def (x,y:index) : x > y <=> y < x.


abstract max_index : index.
axiom [any] max_index (i:index) : i <= max_index.
global axiom [any] index_split (i : index[const]) :
  [forall j, j <= i <=> j = i] \/
  Exists (j:index[const]), [forall k, k < i <=> k <= j].

(** KEM_CPA step using crypto tactic = basic step in hybrid argument *)
global lemma [real/left,real/left] crypto_application (N:index[const]) : equiv(
 skex,
 fun (i,j,k:index) => (skI i, kem_pub (skR j), kR (j, k), rR (j, k)),
 (** diff(real,ideal) encap for key N *)
 fun (j:index) =>
   if (j = N) then
     (fun (i,k:index) =>
        (encap_public (rI (i, j, k)) (kem_pub (skR j)),
         diff(encap_shared (rI (i, j, k)) (kem_pub (skR j)),
              kIfresh (i, j, k))))
   else (fun (_,_:index) => (empty, empty)),
 (** real encap for newer keys and ideal encap for older ones *)
 fun (j:index) =>
   if (j < N) then
     (fun (i,k:index) =>
        (encap_public (rI (i, j, k)) (kem_pub (skR j)),
         kIfresh (i, j, k)))
   else (fun (_,_:index) => (empty, empty)),
 fun (j:index) =>
   if (j > N) then
     (fun (i,k:index) =>
        (encap_public (rI (i, j, k)) (kem_pub (skR j)),
         encap_shared (rI (i, j, k)) (kem_pub (skR j))))
   else (fun (_,_:index) => (empty, empty))
).
Proof.
  by crypto KEM_CPA (skey : skR N).
Qed.

 
(** Note that the system is actually irrelevant here. However it is important to use
   directly the one we'll need in the end, because changing it using transitivity later on
   can be painful. *)
global lemma [real/left,ideal/left] base_case (N:index[const]) :
  equiv(
   (** auxiliary material *)
   skex,
   (fun i j k =>
     (skI i,
      kem_pub (skR j),
      kR (j, k),
      rR (j, k))),
   (** diff(real,ideal) encap for keys up to N *)
   (fun j =>
      if j <= N then
        fun i k =>
          (encap_public (rI (i, j, k)) (kem_pub (skR j)),
           diff(encap_shared (rI (i, j, k)) (kem_pub (skR j)), kIfresh (i, j, k)))
      else fun i k => (empty,empty)),
   (** real encap for newer keys *)
   (fun j =>
      if j > N then
        fun i k =>
          (encap_public (rI (i, j, k)) (kem_pub (skR j)),
           encap_shared (rI (i, j, k)) (kem_pub (skR j)))
      else fun i k => (empty,empty))).
Proof.
  trans [real/left,real/left]; 1,3: refl.
  induction N => N IH.
  have [HN|[P HN]] := index_split N.
  + rewrite HN in 2.
    crypto KEM_CPA (skey : skR N); auto.
  + splitseq 2: (fun j => j = N) (fun _ _ => (empty,empty)).
    assert
      forall j x (y:index->index->message*message), j = N => (if j <= N then x else y) = x
      as H by intro i x y <-.
    rewrite H /= // in 2; clear H.
    rewrite if_then_then -lt_charac in 3.
    (** We have at 3: j<N; at 2: j=N; at 4: j>N.
       The equivalence
         real<N | real=N | real>N ~ ideal<N | ideal=N | real>N
       follows from
         real<N | real=N | real>N ~ ideal<N | real=N | real>N  by IH P
       and
         ideal<N | real=N | real>N ~ ideal<N | ideal=N | real>N by crypto_application.
       We use trans by specifying elements 3 and 2 in the middle sequence. *)
    trans
      3: fun (j:index) =>
           if (j < N) then
             (fun (i,k:index) =>
                (encap_public (rI (i,j,k)) (kem_pub (skR j)),
                 kIfresh (i, j, k)))
           else (fun (i,k:index) => (empty, empty)),
      2: fun (j:index) =>
           if (j = N) then
             (fun (i,k:index) =>
                (encap_public (rI (i,j,k)) (kem_pub (skR j)),
                 encap_shared (rI (i,j,k)) (kem_pub (skR j))))
           else (fun (i,k:index) => (empty, empty)).
    - (** work on conditions before applying IH P *)
      rewrite !HN in 3.
      enrich fun (j:index) =>
        if (j > P) then
          (fun (i,k:index) =>
            (encap_public (rI (i, j, k)) (kem_pub (skR j)),
             encap_shared (rI (i, j, k)) (kem_pub (skR j))))
        else (fun (i,k:index) => (empty, empty)).
       (** 5 and 3 are now subsumed by 0; IMPROVE reasoning e.g. by avoiding gt (>) *)
       assert forall j, j > N <=> j > N && j > P as H1. {. 
         intro j. rewrite (gt_def j N) (gt_def j P). split; 2: auto. intro H. split; 1: auto.
         assert P < N by rewrite HN. by apply (lt_trans P N j).
       }.
       rewrite H1 in 5. deduce 5.
       assert forall j, j = N <=> j = N && j > P as H2. {. 
         intro j. rewrite (gt_def j P). split; 2: auto. intro H. split; 1: auto.
         assert P < N by rewrite HN. auto.
       }.
       rewrite (diff_eq
         (fun (j:index) =>
           if (j = N) then
            (fun i k =>
               (encap_public (rI (i, j, k)) (kem_pub (skR j)),
                encap_shared (rI (i, j, k)) (kem_pub (skR j))))
           else (fun _ _ => (empty, empty)))) in 3.
       rewrite H2 -if_then_then /= in 3. deduce 3.
       apply (IH P).
       by rewrite HN.
    - apply crypto_application N.
Qed.

(** First equivalence real/left vs ideal/left, i.e. with output of the content of sIR. *)
global lemma [real/left,ideal/left] real_ideal_L (tau:timestamp[const]) :
  [happens(tau)]->
  equiv(frame@tau, 
        skex,
        seq(i,j,k:index => (skI(i), 
                            kem_pub(skR(j)), 
                            kR(j,k), rR(j,k), 
                            encap_public (rI (i, j, k)) (kem_pub (skR j)),
                            diff(encap_shared (rI(i,j,k))  (kem_pub (skR(j))), kIfresh(i,j,k))))).
Proof.
  intro Hap.
  induction tau.

  + (** init *)
    expandall.
    fa 0.
    have H := base_case max_index.
    rewrite if_true in H. intro *; apply max_index.
    apply H.
 
  + (** A *)
    rewrite /frame /transcript /exec /output /cond.
    rewrite /state. fa 0. fa !<_,_>. rewrite /input.  fa 1. fa (qatt _).  {constraints. } 
    by apply IH.

  + (** R(j,k) *)
    rewrite /frame /transcript /exec /output /cond /ctR /pkI. 
    fa 0. fa !<_,_>. fa (if _ then _), !<_,_>. fa 6.
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.

  + (** I(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond /ctI.  
    fa 0. 
    fa !<_,_>, (if _ then _), !<_,_>.
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.

  + (** I1(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond /sIR /s /ctI /ctRI /kR2 /kI2. 
    fa 0. fa !<_,_>, (if _ then _). fa 5. fa ! expd (_,_). fa !<_,_>. 
fa 4.     rewrite /ctRI. fa ! exct(_,_). fa 10. rewrite /state /input. fa 1. fa(qatt _). {constraints. }
 by apply IH.

  + (** I2(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>. fa 4. fa 5. fa 5. 
    rewrite /state /input. fa 1. fa(qatt _). { constraints. }
    by apply IH.

  + (** IC(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. rewrite /DctI.  
    fa 0. fa !<_,_>. fa (if _ then _ else _). 
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.

  + (** IC1(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>. 
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.
Qed.


(** Third equivalence: an easy consequence of `real_ideal_L` but it seems hard to
   express this observation in Squirrel. Actually, this ones is even simpler to prove*)
global lemma
  [set:real/left; equiv:ideal/right,real/right] ideal_real_R (tau:timestamp[const]):
  [happens(tau)]->
  equiv(frame@tau, 
        skex,
        seq(i,j,k:index => (
                            kem_pub(skR(j)), kem_pub(skI(i)),
                            rR(j,k), rI(i,j,k)))).
Proof.
  intro Hap.
  induction tau.

  + (** init *)
    expandall. auto. 

  + (** A *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>. 
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.

  + (** R(j,k) *)
    rewrite /frame /transcript /exec /output /cond /ctR /pkI.
    fa 0. fa !<_,_>, if _ then _, !<_,_>. fa 6.
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.

  + (** I(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond /ctI.
    fa 0. fa !<_,_>, (if _ then _), !<_,_>.
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.

  + (** I1(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>, (if _ then _).
    fa 4. fa 5.     
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    fresh 5. (** idealK *)
    * by intro iii jj kk Ord.
    * by apply IH.

  + (** I2(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond.
    fa 0. fa !<_,_>. fa 4. fa 5. fa 5.
    rewrite /state /input. fa 1.  fa(qatt _). {constraints. }
    by apply IH.

  + (** IC(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>. 
    fa 5. rewrite /DctI. 
    rewrite /state /input. fa 1.  fa(qatt _). {constraints. }
    by apply IH.

  + (** IC1(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>.  
    rewrite /state /input. fa 1.  fa(qatt _). {constraints. } 
    by apply IH.
Qed.

set verboseCrypto=true.

name nfresh:message.
(** Second equivalence: strong secrecy on the ideal system. *)
global lemma [ideal] SSec_ideal(tau:timestamp[const]): [happens(tau)]->
  equiv(frame@tau, 
        skex,
        seq(i,j,k:index => (skI(i), 
                            kem_pub(skR(j)), 
                            kR(j,k), 
                            rR(j,k), rI(i,j,k)))).
Proof.
  intro Hap.
  induction tau.

  + (** init *)
    expandall. refl.

  + (** A *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>.     
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH => //.

  + (** R(j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    rewrite /ctR /pkI. 
    fa 0. fa !<_,_>. fa 5. fa 5. fa 6. 
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }    
    by apply IH.

  + (** I(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond /ctI.  
    fa 0. fa !<_,_>. 
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }          
    by apply IH.

  + (** I1(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    rewrite /sIR /s /kI2 /ctI /kR2 /ctRI.
    prf 0, exct (skex, kIfresh (i, j, k)) => //.
    prf 0, expd (_, n_PRF) => //.
    fa 0.  fa !<_,_>. fa 5.

    trans ~left 5:nfresh.
    ++ crypto ~no_subgoal_on_failure XOR_SINGLE.
       by rewrite len_expd namelength_n_PRF1.
    ++ fresh 5 => //.
       fa 4. fa 5.    
       rewrite /state /input. fa 1. fa(qatt _). {constraints. }
       apply IH.
  + (** I2(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>. fa 4. fa 5. fa 5.   
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.

  + (** IC(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>. rewrite /DctI. 
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.

  + (** IC1(i,j,k) *)
    rewrite /frame /transcript /exec /output /cond. 
    fa 0. fa !<_,_>. 
    rewrite /state /input. fa 1. fa(qatt _). {constraints. }
    by apply IH.
Qed.

(** The final strong secrecy result is the consequence of the previous
   lemmas by transitivity. *)
global lemma [set:   real/left;
              equiv: real/left,real/right] SSec_real (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau).
Proof.
  intro Hap.
  trans [ideal/left,ideal/right].
  * (** First equivalence: real versus ideal with sIR. *)
    by apply real_ideal_L.   
  * (** Second equivalence: strong secrecy on ideal system.  *)
    by apply SSec_ideal.
  * (** Third equivalence: ideal versus real with ikIR. *)
    by apply ideal_real_R.
Qed.
