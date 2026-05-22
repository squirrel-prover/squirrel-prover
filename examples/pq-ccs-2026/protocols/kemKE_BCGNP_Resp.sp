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

We prove the strong secrecy of all the keys as seen by the responder when it/ is
interacting with an honest initiator.
Public keys are revealed. 
The responder is ready to answer to an honest or dishonest initiator.
The initiator can also launch a session with a dishonest responder.
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

  oracle o_pub = {
    return (kem_pub skey)
  }
  oracle o_encap_pub = {
    return (encap_public r (kem_pub skey))
  }
  oracle o_encap_shared = {
    return diff(encap_shared r (kem_pub skey), s)
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
    rnd s : message;
    return (
      encap_public r (kem_pub skey),
      diff(encap_shared r (kem_pub skey), s)
    )
  }
}.

game XOR_SINGLE = {
  oracle o_xor(x: message) = {
    rnd n1: message;
    rnd n2: message;
    return if len x = len n1 then diff(xor x n1, n2)
  }
}.


hash exct
hash expd

(** public random key for exct *)

name skex : message.

exact axiom [any] expd_len (x,y:message) : len(expd(x,y)) = namelength_message.

(** long term key of I *)

name skI : index-> kem_skey

(** long term key of R *)
name skR : index->  kem_skey

(** session randomness of I *)
name kI : index * index * index -> message
name rI : index * index * index -> kem_randomness

(** session randomness of R *)
name kR : index * index * index  -> message
name rR : index * index * index -> kem_randomness
abstract DkR: index * index -> message
abstract DrR: index * index -> kem_randomness
name kRfresh : index * index * index  -> message

(** ideal key *)
name idealKD : index * index -> message

(** material revealed to the attacker *)
abstract DkI: index * index * index -> message.
abstract DrI: index * index * index -> kem_randomness.
abstract DskR: index -> kem_skey.

abstract ok:message

channel cI
channel cR
(** mutable sIR(i,j,k:index) : message =  zero. *)
mutable sRI(j,k:index) : message = zero.


set processStrictLetMode = true.

process Init(i,j,k:index) =
   let ctI = encap_public (rI(i,j,k)) (kem_pub (skR(j))) in
   out(cI, <kem_pub(skI(i)), ctI>);
   (** public key is revealed *)
   in(cR,xtR).
   (** Then the key is computed but never used, thus we do not model this part. *)


process InitToCompromised(i,j,k:index) =
   let DctI = encap_public (DrI(i,j,k))  (kem_pub (DskR(j))) in
   out(cI, <kem_pub(skI(i)), DctI>);
   (** public key is revealed *)
   in(cR,xtR).
   (** Then the key is computed but never used, thus we not model this part *)

(** The try find instruction may seem artificial but without this instruction,
   we cannot introduce the index i, and in the end it is not possible to enrich
   the first equivalence below with
   i,j,k => encap(diff(kR(i,j,k),kRfresh(i,j,k)), rR(i,j,k), pk(skI i)).
   This enrich is important to prove the inital case easily.
   In other words, removing this try find means that we
   have to find another way to do the proof. *)

process RespReal(j,k:index) =
   in(cI, xtI);
   let pkI = fst(xtI) in
   let ctIR = snd(xtI) in
   let ctR =
     try find i such that pkI = kem_pub(skI(i))
     in encap_public (rR(i,j,k)) (kem_pub(skI(i)))
     else encap_public (DrR(j,k)) pkI
   in out(cR,<kem_pub(skR(j)),ctR>);
   in (cR,xdummy);
   let kI2 = exct(skex, (decap ctIR (skR(j))) ) in
   let s = <pkI,<ctIR,<kem_pub(skR(j)),ctR>>> in
   let kR2 =
     try find i such that pkI = kem_pub(skI(i))
     in exct(skex,encap_shared (rR(i,j,k)) pkI)
     else exct(skex, encap_shared (DrR(j,k)) pkI)
   in sRI j k := expd(s,kI2) XOR expd(s,kR2);
   if (exists i:index,  pkI = kem_pub(skI(i)))
   then out(cR,diff((sRI j k),idealKD(j,k))).

process RespIdeal(j,k:index) =
   in(cI, xtI);
   let pkI = fst(xtI) in
   let ctIR = snd(xtI) in
   let ctR =
     try find i such that pkI = kem_pub(skI(i))
     in encap_public  (rR(i,j,k))  (kem_pub(skI(i)))
     else encap_public  (DrR(j,k)) pkI
   in out(cR,<kem_pub(skR(j)),ctR>);
   in (cR,xdummy);
   let kI2 = exct(skex, (decap ctIR (skR(j))) ) in
   let s = <pkI,<ctIR,<kem_pub(skR(j)),ctR>>> in
   let kR2 =
     try find i such that pkI = kem_pub(skI(i))
     in exct(skex,kRfresh(i,j,k))
     else exct(skex, (encap_shared (DrR(j,k)) pkI))
   in sRI j k := expd(s,kI2) XOR expd(s,kR2);
   if (exists i:index,  pkI = kem_pub(skI(i))) then
   out(cR,diff((sRI j k),idealKD(j,k))).


system [postquantum] real =
  out(cI,skex);
  ((!_j !_k R: RespReal(j,k)) |
   (!_i !_j !_k I: Init(i,j,k)) |
   (!_i !_j !_k IC: InitToCompromised(i,j,k))).

system [postquantum] ideal =
  out(cI,skex);
  ((!_j !_k R: RespIdeal(j,k)) |
   (!_i !_j !_k I: Init(i,j,k)) |
   (!_i !_j !_k IC: InitToCompromised(i,j,k))).


(** Preliminaries *)

lemma [real/left,real/left] diff_eq ['a] (x:'a) : diff(x,x) = x.
Proof. by project. Qed.
axiom [any] gt_def (x,y:index) : x > y <=> y < x.


(** Improvement: custom_try_true_1 to be replaced by try_true_1 *)

lemma [any] custom_try_true_1 ['a 'b] :
  forall (phi:'a->bool, f:'a->'b, g:'b),
    (exists x, phi x) =>
    try find x:'a such that phi x in f x else g =
    f (choose phi).
Proof.
  intro phi f g H.
  rewrite try_carac_1.
  rewrite if_true => //.
Qed.

(** First equivalence *)

abstract max_index : index.
axiom [any] max_index (i:index) : i <= max_index.
global axiom [any] index_split (i : index[const]) :
  [forall j, j <= i <=> j = i] \/
  Exists (j:index[const]), [forall k, k < i <=> k <= j].

(** KEM_CPA step using crypto tactic = basic step in hybrid argument *)
global lemma [real/left,real/left] crypto_application (N:index[const]) : equiv(
 skex,
 fun (i,j,k:index) => (skR j, kem_pub (skI i), kI (i, j, k), rI (i, j, k), kR (i, j, k), idealKD (j,k)),
 (** diff(real,ideal) encap for key N *)
 fun (i:index) =>
   if (i = N) then
     (fun (j,k:index) =>
        (encap_public (rR (i, j, k)) (kem_pub (skI i)),
         diff(encap_shared (rR (i, j, k)) (kem_pub (skI i)),
              kRfresh (i, j, k))))
   else (fun (_,_:index) => (empty, empty)),
 (** real encap for newer keys and ideal encap for older ones *)
 fun (i:index) =>
   if (i < N) then
     (fun (j,k:index) =>
        (encap_public (rR (i, j, k)) (kem_pub (skI i)),
         kRfresh (i, j, k)))
   else (fun (_,_:index) => (empty, empty)),
 fun (i:index) =>
   if (i > N) then
     (fun (j,k:index) =>
        (encap_public (rR (i, j, k)) (kem_pub (skI i)),
         encap_shared (rR (i, j, k)) (kem_pub (skI i))))
   else (fun (_,_:index) => (empty, empty))
).
Proof.
  by crypto KEM_CPA (skey : skI N).
Qed.


(** Note that the system is actually irrelevant here. However it is important to use
   directly the one we'll need in the end, because changing it using transitivity later on
   can be painful. *)
global lemma [real/left,ideal/left] base_case (N:index[const]) :
  equiv(
   (** auxiliary material *)
   skex,
   fun (i,j,k:index) => (skR j, kem_pub (skI i), kI (i, j, k), rI (i, j, k), kR (i, j, k), idealKD (j,k)),
   (** diff(real,ideal) encap for keys up to N *)
   (fun i =>
      if i <= N then
        fun j k =>
          (encap_public (rR (i, j, k)) (kem_pub (skI i)),
           diff(encap_shared (rR (i, j, k)) (kem_pub (skI i)), kRfresh (i, j, k)))
      else fun j k => (empty,empty)),
   (** real encap for newer keys *)
   (fun i =>
      if i > N then
        fun j k =>
          (encap_public (rR (i, j, k)) (kem_pub (skI i)),
           encap_shared (rR (i, j, k)) (kem_pub (skI i)))
      else fun j k => (empty,empty))).
Proof.
  trans [real/left,real/left]; 1,3: refl.
  induction N => N IH.
  have [HN|[P HN]] := index_split N.
  + rewrite HN in 2.
    by crypto KEM_CPA (skey : skI N).
  + splitseq 2: (fun i => i = N) (fun _ _ => (empty,empty)).
    assert
      forall i x (y:index->index->message*message), i = N => (if i <= N then x else y) = x
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
      3: fun (i:index) =>
           if (i < N) then
             (fun (j,k:index) =>
                (encap_public (rR (i,j,k)) (kem_pub (skI i)),
                 kRfresh (i, j, k)))
           else (fun _ _ => (empty, empty)),
      2: fun (i:index) =>
           if (i = N) then
             (fun (j,k:index) =>
                (encap_public (rR (i,j,k)) (kem_pub (skI i)),
                 encap_shared (rR (i,j,k)) (kem_pub (skI i))))
           else (fun _ _ => (empty, empty)).
    - (** work on conditions before applying IH P *)
      rewrite !HN in 3.
      enrich fun (i:index) =>
        if (i > P) then
          (fun (j,k:index) =>
            (encap_public (rR (i, j, k)) (kem_pub (skI i)),
             encap_shared (rR (i, j, k)) (kem_pub (skI i))))
        else (fun _ _ => (empty, empty)).
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
         (fun (i:index) =>
           if (i = N) then
            (fun j k =>
               (encap_public (rR (i, j, k)) (kem_pub (skI i)),
                encap_shared (rR (i, j, k)) (kem_pub (skI i))))
           else (fun _ _ => (empty, empty)))) in 3.
       rewrite H2 -if_then_then /= in 3. deduce 3.
       apply (IH P).
       by rewrite HN.
    - apply crypto_application N.
Qed.

global theorem [real/left,ideal/left] real_ideal (tau:timestamp[const]) :
  [happens(tau)]->
  equiv(frame@tau, skex,
        seq(i,j,k:index => (skR(j),
                            kem_pub(skI(i)),
                            kI(i,j,k), rI(i,j,k), kR(i,j,k),
                            encap_public (rR (i, j, k)) (kem_pub (skI i)),
                            diff(encap_shared (rR(i,j,k)) (kem_pub(skI i)), kRfresh(i,j,k)),
                            idealKD(j,k)))).

Proof.
intro Hap. induction tau.

(** init *)
+ rewrite /frame. fa 0. fa 2.
  have H := base_case max_index.
  rewrite if_true in H. intro *; apply max_index.
  apply H.

 (** A *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.

 (** R *)
+ rewrite /frame  /transcript /exec /cond /output /ctR /pkI.
  fa 0. fa !<_,_>. fa(if _ then _ else _). fa !<_,_>. 
  fa 6.  fa 6. rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.


 (** R1 *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. 
  rewrite /sRI /s /kI2 /kR2 /ctIR /ctR /pkI. 

(** replacement of an occurrence of (fst (input@R(j, k))) by (kem_pub (skI i)) 
in the then branch of a try find *)
assert(
if (exec@pred (R1(j, k)) &&
       exists (i:index), fst (input@R(j, k)) = kem_pub (skI i)) then
     xor
       (expd
          (<fst (input@R(j, k)),
            <snd (input@R(j, k)),
             <kem_pub (skR j),
              try find i:index such that
                (fst (input@R(j, k)) = kem_pub (skI i))
              in encap_public (rR (i, j, k)) (kem_pub (skI i))
              else encap_public (DrR (j, k)) (fst (input@R(j, k)))>>>,
           exct (skex, decap (snd (input@R(j, k))) (skR j))))
       (expd
          (<fst (input@R(j, k)),
            <snd (input@R(j, k)),
             <kem_pub (skR j),
              try find i:index such that
                (fst (input@R(j, k)) = kem_pub (skI i))
              in encap_public (rR (i, j, k)) (kem_pub (skI i))
              else encap_public (DrR (j, k)) (fst (input@R(j, k)))>>>,
           try find i:index such that (fst (input@R(j, k)) = kem_pub (skI i))
           in
             exct
               (skex,
                diff(encap_shared (rR (i, j, k)) (fst (input@R(j, k))),
                  kRfresh (i, j, k)))
           else exct (skex, encap_shared (DrR (j, k)) (fst (input@R(j, k))))))

=

if (exec@pred (R1(j, k)) &&
       exists (i:index), fst (input@R(j, k)) = kem_pub (skI i)) then
     xor
       (expd
          (<fst (input@R(j, k)),
            <snd (input@R(j, k)),
             <kem_pub (skR j),
              try find i:index such that
                (fst (input@R(j, k)) = kem_pub (skI i))
              in encap_public (rR (i, j, k)) (kem_pub (skI i))
              else encap_public (DrR (j, k)) (fst (input@R(j, k)))>>>,
           exct (skex, decap (snd (input@R(j, k))) (skR j))))
       (expd
          (<fst (input@R(j, k)),
            <snd (input@R(j, k)),
             <kem_pub (skR j),
              try find i:index such that
                (fst (input@R(j, k)) = kem_pub (skI i))
              in encap_public (rR (i, j, k)) (kem_pub (skI i))
              else encap_public (DrR (j, k)) (fst (input@R(j, k)))>>>,
           try find i:index such that (fst (input@R(j, k)) = kem_pub (skI i))
           in
             exct
               (skex,
                diff(encap_shared (rR (i, j, k)) (kem_pub (skI i)),
                  kRfresh (i, j, k)))
           else exct (skex, encap_shared (DrR (j, k)) (fst (input@R(j, k))))))).
 {
fa => //.
intro [H1 H2]. 
fa => //. fa . fa => //. 
case (try find _ such that _ in  _ else _). 
 ++ intro [i [HH1 HH2]].
    fa => //. 
 ++ intro [HH1 HH2]. 
    destruct H2 as [i0 h2]. use HH1 with i0. auto. 
auto.  
}

rewrite H in 5. 
clear H. 
(** because of the conditional at top level, we know that the try find is true *)
rewrite !custom_try_true_1  => //.
deduce 5. deduce 4. 

rewrite /state /input. 
fa 1. fa(qatt _). {constraints. }
by apply IH.


 (** R2 *)
+ rewrite /frame  /transcript /exec /cond /output /pkI.
  fa 0. fa !<_,_>. 
  deduce 4.   
  rewrite /state /input.
  fa 1. fa(qatt _). { constraints.  }
  by apply IH. 

 (** I *)
+ rewrite /frame  /transcript /exec /cond /output /ctI.
  fa 0. fa !<_,_>. 
  deduce 5. 
  rewrite /state /input.
  fa 1. fa(qatt _). { constraints. }
  by apply IH. 

 (** I1 *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. 
  rewrite /state /input.
  fa 1. fa(qatt _). { constraints. }
  by apply IH. 

 (** IC *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. 
  rewrite /state /input.
  fa 1. fa(qatt _). { constraints. }
  by apply IH. 

 (** IC1 *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. 
  rewrite /state /input.
  fa 1. fa(qatt _). { constraints. }
  by apply IH. 
Qed.


name nfresh: message.

(** Strong secrecy of the initiator key in the ideal system *)
global theorem [ideal] SSec_ideal(tau:timestamp[const]):
  [happens(tau)]->
  equiv(frame@tau, skex,
        seq(i,j,k:index => (skR(j), skI(i), rI(i,j,k), rR(i,j,k)))).

Proof.
  intro Hap.
  induction tau.

  (** init *)
  + rewrite /frame.
    auto.

  (** A *)
  + rewrite /frame /transcript /exec /cond /output.
    fa 0. fa !<_,_>.
    rewrite /state /input.
    fa 1. fa(qatt _). { constraints. }
    apply IH.

  (** R(i,j) *)
  + rewrite /frame /transcript /exec /cond /output /ctR.
    fa 0. fa !<_,_>. deduce 5.
    rewrite /state /input.
    fa 1. fa(qatt _). { constraints. }
    apply IH.
  
  (** R1(j,k) *)
  + rewrite /frame /transcript /exec /cond /output.
    fa 0. fa  !<_,_>.
    rewrite /sRI /s /pkI /ctIR /kI2 /ctR /ctIR /kR2.
    rewrite !custom_try_true_1; try auto.

    reduce.
    have Ord := depends_R_R1 j k.
    prf 5,  exct (skex,   kRfresh (_,_,_)). {.

    intro [h0 [ii h1]]. repeat split.
    ++ intro i0 j0 k0. intro [H1 | H2]. intro Hap'. intro hh. intro [Eq1 Eq2 Eq3].
       rewrite  Eq2 Eq3 in H1.  auto.
       intro Hap'. intro hh. intro [Eq1 Eq2 Eq3].
       rewrite Eq2 Eq3 in H2.
       use depends_R_R1 with j0, k0. auto. auto.

    ++ intro i0 j0 k0. intro [H1 | H2]. intro Hap'. intro [Eq1 Eq2 Eq3].
       rewrite  Eq2 Eq3 in H1.  auto.
       intro Hap'. intro [Eq1 Eq2 Eq3].
       rewrite  Eq2 Eq3 in H2.
       use depends_R_R1 with j0, k0. auto. auto.
    ++ intro i0 j0 k0. intro [H1 | H2]. intro hh.  intro [Eq1 Eq2 Eq3].
       rewrite  Eq2 Eq3 in H1.
       use mutex_R1_R2 with j0, k0. auto.
       intro hh. intro [Eq1 Eq2 Eq3].
       rewrite Eq2 Eq3 in H2.
       use mutex_R1_R2 with j0, k0. auto.

    }.

    prf 5, expd (_, n_PRF).
    auto.
    fa 5.

    have ? : R(j,k) < R1(j,k) by constraints.

    trans ~left 5:nfresh. 
    ++ crypto ~no_subgoal_on_failure XOR_SINGLE.
       by rewrite expd_len namelength_n_PRF1.
    ++ fresh 5 => //. 
       deduce 4. 
       rewrite /state /input. fa 1. fa(qatt _). {constraints. }
       apply IH.


  (** R2(j,k) *)
  + rewrite /frame /transcript /exec /cond /output.
    fa 0. fa !<_,_>. deduce 4.
    rewrite /state /input.
    fa 1. fa(qatt _). { constraints. }
    apply IH.

  (** I(i,j,k) *)
  + rewrite /frame /transcript /exec /cond /output.
    fa 0. fa !<_,_>. deduce 4.
    rewrite /state /input.
    fa 1. fa(qatt _). { constraints. }
    apply IH.

  (** I1(i,j,k) *)
  + rewrite /frame /transcript /exec /cond /output.
    fa 0. fa !<_,_>. 
    rewrite /state /input.
    fa 1. fa(qatt _). { constraints. }
    apply IH.

  (** IC(i,j,k) *)
  + rewrite /frame /transcript /exec /cond /output.
    fa 0. fa !<_,_>. 
    rewrite /state /input.
    fa 1. fa(qatt _). { constraints. }
    apply IH.

  (** IC1(i,j,k) *)
  + rewrite /frame /transcript /exec /cond /output.
    fa 0. fa !<_,_>. 
    rewrite /state /input.
    fa 1. fa(qatt _). { constraints. }
    apply IH.
Qed.


(** Third equivalence *)
(** Similar to the first equivalence but actually simpler to prove: no need to apply cpa on a sequence *)
global theorem [set: real/left; equiv: ideal/right,real/right] ideal_real (tau:timestamp[const]) : [happens(tau)]->
  equiv(frame@tau, skex,
        seq(i,j,k:index => (skR(j),
                            skI(i),
                            rI(i,j,k), rR(i,j,k), idealKD(j,k)))).

Proof.
intro Hap. induction tau.

(** init *)
+ rewrite /frame. 
  auto. 

(** A *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.

(** R *)
+ rewrite /frame  /transcript /exec /cond /output /ctR /pkI.
  fa 0. fa !<_,_>. fa(if _ then _ else _). fa !<_,_>. 
  fa 6.  fa 6. rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.

(** R1 *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. deduce 4. fa 4.  deduce 4. 
  rewrite /state /input. 
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.

(** R2(j,k) *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. deduce 4.  rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.

(** I(i,j,k) *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.

(** I1(i,j,k) *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.

(** IC(i,j,k) *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.

(** IC1(i,j,k) *)
+ rewrite /frame  /transcript /exec /cond /output.
  fa 0. fa !<_,_>. rewrite /state /input.
  fa 1. fa(qatt _). {constraints. }  
  by apply IH.
Qed.


(** Strong secrecy of the responder key in the real system *)
global theorem [set: real/left; equiv:real/left, real/right]  SSec_real(tau:timestamp[const]):
  [happens(tau)]->
  equiv(frame@tau).
Proof.
 intro Hap.
 trans [ideal/left,ideal/right].
 + (** normal left / ideal left *)
   by apply real_ideal.
 + (** ideal left / ideal right *)
   by apply SSec_ideal.
 + (** ideal right / normal right *)
   by apply ideal_real.
Qed.
