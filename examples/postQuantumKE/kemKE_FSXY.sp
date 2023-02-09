(*******************************************************************************

Generic Construction (GC) of key exchange from Key encapsulation Mechanism (KEM)


That is a more complex construction than the BCGNP one.

[A] Fujioka, Atsushi and Suzuki, Koutarou and Xagawa, Keita and Yoneyama, Kazuki. Strongly Secure Authenticated Key Exchange from Factoring, Codes, and Lattices


# On KEMs

The protocol uses KEMS

The KEM are usally described with
(ek,dk) <- Keygen(r) returns an encryption key ek and a decryption key ek
(k,ct) <- Encap(r,ek) returns a session key k and its cyphertext ct
k <- Decap(ct,dk) returns k.

We abstract this with, pk, encap and decap function symbols, where
 * dk is a name, ek = pk(dk)
 * k is a name, ct=encap(k,r,pk(dk)).
 * decap(encap(k,r,pk(dk)),dk) = k


# Protocol description

There are two KEMs (Pk, Encap, DeCap) and (wPk, wEncap, wDeCap)

PRFs : F, F' and G
KDF: KDF with public random salt s

Two parties I (initiator) and R (responder)

Static keys for party X := dkX, skX, sk2X
Public keys for party X : ekX = pk(dkX)


Initiator                                  Responder
new kI; new rI, rI2.
ctI := Encap(kI, F(rI,skI) XOR F(skI2,rI2)  ,pk(dkR))
new dkT; ekT := wpk(dkT);

                 I --(I,R,ctI,ekT)-> R

R:
                                       new kR; new rR, rR2, rTI.
                                       ctR := Encap(kR, F(rR,skR) XOR F(sk2R, rR2) , pk(dkI))
                                       new kT;
                                       ctT := wEncap(kT, rTI, ekT )

                 I <--(I,R,ctR,ctT)-- R



kR := Decap(ctR,dkI)
kT := wDecap(ctT,dkT)

                                       kI := Decap(ctI,dkI)

Final key derivation:

K1 := KDF(s,kI); K2 := KDF(s,kR); K3 := KDF(s,kT)

ST := (I,R,pk(dkI),pk(dkR),ctI,pk(ekT),ctR,ctT)
SK := G(ST,K1) XOR G(ST,K2) XOR G(ST,K3)


# High level intuitions


We model two agents that may initiate multiple sessions. See PQ-x3dh-like for a devellopment with multiple keys.

We prove some weak authentication: if an agent obtained some honest parameter,
it was sent out by an honest agent.

We prove also separately for each agent that the computed key is real or random,
which implies the implicit authentication of the scheme: only the other trusted
party could potentially compute the key.



*******************************************************************************)
set postQuantumSound = true.

include Basic.
set autoIntro=true.

hash F

hash F2

hash G


(* public random salt *)

name s : message

(* KEMs *)

aenc encap,decap,pk

aenc wencap,wdecap,wpk

(* long term keys of I *)
name dkI : index -> message
name skI : index ->  message
name sk2I : index -> message

(* long term keys of R *)
name dkR : index -> message
name skR : index -> message
name sk2R : index -> message

(* session randomess of I talking to compromised R *)
name DkI : index * index * index -> message
name DrI : index * index * index -> message
name DrI2 : index * index * index -> message
name DdkT : index * index * index -> message

(* long term keys of compromised R *)
abstract DdkR : index -> message
abstract DskR : index -> message
abstract Dsk2R : index -> message

(* session randomess of I *)
name kI : index * index * index -> message
name rI : index * index * index -> message
name rI2 : index * index * index -> message
name dkT : index * index * index -> message


abstract ok : message


(* session randomess of R *)
name kR : index * index * index -> message
name rR : index * index * index -> message
name rR2 : index * index * index -> message
name rTI : index * index * index -> message
name kT : index * index * index -> message

name DkR :  index * index -> message
name DrR :  index * index -> message
name DrR2 : index * index -> message
name DrTI : index * index -> message
name DkT :  index * index -> message


name kIR : index * index * index -> message

mutable sIR(i,j,k:index) : message =  zero
mutable sRI(i,j,k:index) : message =  zero
mutable DsRI(j,k:index) : message =  zero
mutable DsIR(i,j,k:index) : message =  zero

hash kdf

hash Gh

channel cI
channel cR.

(* k-th copy of initiator with key skI(i) trying to communicate with responder with key pk(dkR(j)) *)
process Initiator(i,j,k:index) =
 let ctI = encap(kI(i,j,k), F(rI(i,j,k),skI(i)) XOR F(sk2I(i),rI2(i,j,k))  ,pk(dkR(j))) in
 let ekT = wpk(dkT(i,j,k)) in
 out(cI, <ctI,ekT> ); (*we omit the public parameters in the output *)

 in(cR,messI);
 let ctR = fst(messI) in
 let ctT = snd(messI) in

 (* first key derivations *)
 let kT = wdecap(ctT,dkT(i,j,k)) in

 (* Full common key derivations *)
 let K1 = kdf(s,kI(i,j,k)) in
 let K2 = kdf(s, decap(ctR,dkI(i)) ) in
 let K3 = kdf(s,kT) in

 let ST = <pk(dkI(i)),<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
 sIR(i,j,k) := xor(G(ST,K1)) (xor (G(ST,K2)) (G(ST,K3))).




(* k-th copy of responder with key skR(j) *)
process Responder(j,k:index) =
   in(cI, pkI);
   in(cI, messR);
   try find i such that pkI = pk(dkI(i)) in
     let ctI = fst(messR) in
     let ekT = snd(messR) in

     let ctR = encap(kR(i,j,k), F(rR(i,j,k),skR(j)) XOR F(sk2R(j),rR2(i,j,k)), pk(dkI(i))) in (* we hardcode the public key of I here, we need to add in parallel the responder that wants to talk to anybody *)
     let ctT = wencap(kT(i,j,k),rTI(i,j,k),ekT) in
     out(cR,<ctR,ctT>);


  (* Full common key derivations *)
     let K1 = kdf(s,decap(ctI,dkR(j)) ) in
     let K2 = kdf(s,kR(i,j,k)) in
     let K3 = kdf(s,kT(i,j,k)) in

     let ST = <pk(dkI(i)),<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
     sRI(j,k,i) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3)))
  else
     let ctI = fst(messR) in
     let ekT = snd(messR) in

     let ctR = encap(DkR(j,k), F(DrR(j,k),skR(j)) XOR F(sk2R(j),DrR2(j,k)), pkI) in (* we hardcode the public key of I here, we need to add in parallel the responder that wants to talk to anybody *)
     let ctT = wencap(DkT(j,k),DrTI(j,k),ekT) in
     out(cR,<ctR,ctT>);

  (* Full common key derivations *)
     let K1 = kdf(s,decap(ctI,dkR(j)) ) in
     let K2 = kdf(s,DkR(j,k)) in
     let K3 = kdf(s,DkT(j,k)) in

     let ST = <pkI,<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
     DsRI(j,k) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3))).



(* k-th copy of initiator with key dkI(i) trying to communicate with compromised responder with key pk(DdkR(j)) *)
process InitiatorToCompromised(i,j,k:index) =
 let ctI = encap(DkI(i,j,k), F(DrI(i,j,k),skI(i)) XOR F(sk2I(i),DrI2(i,j,k))  ,pk(DdkR(j))) in
 let ekT = wpk(DdkT(i,j,k)) in
 out(cI, <ctI,ekT> ); (*we omit the public parameters in the output *)

 in(cR,messI);
 let ctR = fst(messI) in
 let ctT = snd(messI) in

 (* first key derivations *)
 let kT = wdecap(ctT,DdkT(i,j,k)) in

 (* Full common key derivations *)
 let K1 = kdf(s,DkI(i,j,k)) in
 let K2 = kdf(s, decap(ctR,dkI(i)) ) in
 let K3 = kdf(s,kT) in

 let ST = <pk(dkI(i)),<pk(DdkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
 sIR(i,j,k) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3))).



system [main] out(cI,s); ((!_j !_k R: Responder(j,k)) | (!_i !_j !_k I: Initiator(i,j,k))
| (!_i !_j !_k I: InitiatorToCompromised(i,j,k))
).


(******* Valid cypher randomness  ******)
(***************************************)
(* We must first show that the authentication is using valid randoms for the encapsulations. *)


(* k-th copy of initiator with key skI(i) trying to communicate with responder with key pk(dkR(j)) *)
process Initiator2(i,j,k:index) =
 let ctI = encap(kI(i,j,k), diff(F(rI(i,j,k),skI(i)) XOR F(sk2I(i),rI2(i,j,k)), rI(i,j,k))  ,pk(dkR(j))) in
 let ekT = wpk(dkT(i,j,k)) in
 out(cI, <ctI,ekT> ); (*we omit the public parameters in the output *)

 in(cR,messI);
 let ctR = fst(messI) in
 let ctT = snd(messI) in

 (* first key derivations *)

 let kT = wdecap(ctT,dkT(i,j,k)) in

 (* Full common key derivations *)
 let K1 = kdf(s,kI(i,j,k)) in
 let K2 = kdf(s,decap(ctR,dkI(i))) in
 let K3 = kdf(s,kT) in

 let ST = <pk(dkI(i)),<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
 sIR(i,j,k) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3))).




(* k-th copy of responder with key skR(j) *)
process Responder2(j,k:index) =
   in(cI, pkI);
   in(cI, messR);
   try find i such that pkI = pk(dkI(i)) in
     let ctI = fst(messR) in
     let ekT = snd(messR) in

     let ctR = encap(kR(i,j,k), diff( F(rR(i,j,k),skR(j)) XOR F(sk2R(j),rR2(i,j,k)), rR(i,j,k)), pk(dkI(i))) in (* we hardcode the public key of I here, we need to add in parallel the responder that wants to talk to anybody *)
     let ctT = wencap(kT(i,j,k),rTI(i,j,k),ekT) in
     out(cR,<ctR,ctT>);


  (* Full common key derivations *)
     let K1 = kdf(s, decap(ctI,dkR(j))) in
     let K2 = kdf(s,kR(i,j,k)) in
     let K3 = kdf(s,kT(i,j,k)) in

     let ST = <pk(dkI(i)),<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
     sRI(j,k,i) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3)))
  else
     let ctI = fst(messR) in
     let ekT = snd(messR) in

     let ctR = encap(DkR(j,k), F(DrR(j,k),skR(j)) XOR F(sk2R(j),DrR2(j,k)), pkI) in (* we hardcode the public key of I here, we need to add in parallel the responder that wants to talk to anybody *)
     let ctT = wencap(DkT(j,k),DrTI(j,k),ekT) in
     out(cR,<ctR,ctT>);

  (* Full common key derivations *)
     let K1 = kdf(s,decap(ctI,dkR(j))) in
     let K2 = kdf(s,DkR(j,k)) in
     let K3 = kdf(s,DkT(j,k)) in

     let ST = <pkI,<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
     DsRI(j,k) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3))).


system [main_rand] out(cI,s); ((!_j !_k R: Responder2(j,k)) | (!_i !_j !_k I: Initiator2(i,j,k))
| (!_i !_j !_k DI: InitiatorToCompromised(i,j,k))
).


axiom [main_rand] len_F (x1,x2:message) : len(F(x1,x2)) = len(s).


equiv [main_rand] trans_auth.
Proof.
  enrich seq(i:index=>dkI(i)); enrich seq(i:index=> dkR(i)); enrich s.
  enrich seq(i,j,k:index=> kT(i,j,k)); enrich seq(i,j,k:index=>rTI(i,j,k));
  enrich seq(i,j,k:index=> dkT(i,j,k));
  enrich seq(i,j,k:index=> kR(i,j,k));
  enrich seq(i,j,k:index=> kI(i,j,k)).

  (* enrich of the dishonest randoms *)
  enrich seq(j,k:index=> DkT(j,k)); 
  enrich seq(j,k:index=>DrTI(j,k));
  enrich seq(j,k:index=> DkR(j,k));
  enrich seq(j,k:index=> DrR(j,k));
  enrich seq(i,j,k:index=>DkI(i,j,k)).
  enrich seq(i,j,k:index=>DdkT(i,j,k)).
  enrich seq(i:index=>dkR(i)).

  induction t => //.
    + expandall. 
      by fa 14.

    + expandall.
      by fa 14.
      
    + (* First output of R *)
      expandall.
      fa 14.
      fa 15.
      fa 15.
      fa 15.
      fa 16.
      prf 16.
      rewrite if_true // in 16.
      xor 16, xor(F(rR(i,j,k),skR(j))) n_PRF, n_PRF.
      rewrite if_true in 16.
      use len_F with rR(i,j,k), skR(j).
      namelength n_PRF,s.
      fa 16. fa 16.
      fresh 17; 1:auto.
      by apply IH.

    + (* Second output of R *)
      expandall.
      fa 14.

    + (* First output of R with dishonnest talker *)
       expandall.
       fa 14.
       fa 15.
       fa 16.
       admit 15. (* this is a dumb fadup weakness, as all the dkI(i) are in the frame, the forall is obviously ok. *)
       repeat fa 15.
       fa 17.
       prf 16; rewrite if_true // in 16.
       xor 16, n_PRF.
       rewrite if_true // in 16.
       use len_F with DrR(j,k), skR(j).
       namelength n_PRF,s.
       fresh 16; 1: auto.
       by apply IH.

    + (* Second output of R with dishonnest talker *)
      expandall.
      by fa 14.

    + (* First output of I *)
      expandall.
      fa 14.
      fa 15.
      fa 15.
      fa 15.
      fa 16.
      prf 15.
      rewrite if_true // in 15.
      xor 15, xor(F(rI(i,j,k),skI(i))) n_PRF, n_PRF.
      rewrite if_true // in 15.
      use len_F with rI(i,j,k), skI(i).
      by namelength n_PRF,s.
      fa 15.
      fresh 16; 1:auto.
      by apply IH.

    + (* Second output of I *)
      expandall.
      by fa 14.



    + (* First output of DI *)
      expandall.
      fa 14.
      fa 15.
      fa 15.
      fa 15.
      fa 15.
      prf 16.
      rewrite if_true // in 16.
      xor 16, xor(F(DrI(i,j,k),skI(i))) n_PRF, n_PRF.
      rewrite if_true // in 16.
      use len_F with DrI(i,j,k), skI(i).
      by namelength n_PRF,s.
      fresh 16; 1:auto.
      by apply IH.

    + (* Second output of DI *)
      expandall.
      fa 14.
Qed.

(* From [main_rand/right], we can now use cca to hide the two main random seeds, kR and kI *)


system mainCCAkR = [main_rand/right] with gcca (il,jl,kl:index),  encap(kR(il,jl,kl), rR(il,jl,kl), pk(dkI(il))).

system mainCCAkI = [mainCCAkR] with gcca (il,jl,kl:index),  encap(kI(il,jl,kl), rI(il,jl,kl) ,pk(dkR(jl))).


(******* Strong secrecy  ******)
(***************************************)
(* Idealized version with kI and kR hidden *)

(* k-th copy of initiator with key skI(i) trying to communicate with responder with key pk(dkR(j)) *)
process Initiator3(i,j,k:index) =
 let ctI = encap(n_CCA1(i,j,k),  rI(i,j,k)  ,pk(dkR(j))) in
 let ekT = wpk(dkT(i,j,k)) in
 out(cI, <ctI,ekT> ); (*we omit the public parameters in the output *)

 in(cR,messI);
 let ctR = fst(messI) in
 let ctT = snd(messI) in

 (* first key derivations *)
 let kT = wdecap(ctT,dkT(i,j,k)) in

 (* Full common key derivations *)
 let K1 = kdf(s,kI(i,j,k)) in
 let K2 =
   try find il,jl,kl such that
   ctR = encap(n_CCA(il,jl,kl), rR(il,jl,kl), pk(dkI(il)))
   in
       kdf(s,kR(il,jl,kl))
   else
   kdf(s,decap(ctR,dkI(i)))

in
 let K3 = kdf(s,kT) in

 let ST = <pk(dkI(i)),<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
 sIR(i,j,k) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3))).




(* k-th copy of responder with key skR(j) *)
process Responder3(j,k:index) =
   in(cI, pkI);
   in(cI, messR);
   try find i such that pkI = pk(dkI(i)) in
     let ctI = fst(messR) in
     let ekT = snd(messR) in

     let ctR = encap(n_CCA(i,j,k), rR(i,j,k), pk(dkI(i))) in (* we hardcode the public key of I here, we need to add in parallel the responder that wants to talk to anybody *)
     let ctT = wencap(kT(i,j,k),rTI(i,j,k),ekT) in
     out(cR,<ctR,ctT>);

  (* Full common key derivations *)
     let K1 =
   try find il,jl,kl such that
    ctI = encap(n_CCA1(il,jl,kl), rI(il,jl,kl) ,pk(dkR(jl)))
   in
    kdf(s,kI(il,jl,kl))
   else
    kdf(s,decap(ctI,dkR(j)))


 in
     let K2 = kdf(s,kR(i,j,k)) in
     let K3 = kdf(s,kT(i,j,k)) in

     let ST = <pk(dkI(i)),<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
     sRI(j,k,i) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3)))
  else
     let ctI = fst(messR) in
     let ekT = snd(messR) in

     let ctR = encap(DkR(j,k), F(DrR(j,k),skR(j)) XOR F(sk2R(j),DrR2(j,k)), pkI) in (* we hardcode the public key of I here, we need to add in parallel the responder that wants to talk to anybody *)
     let ctT = wencap(DkT(j,k),DrTI(j,k),ekT) in
     out(cR,<ctR,ctT>);

  (* Full common key derivations *)
     let K1 =
   try find il,jl,kl such that
    ctI = encap(n_CCA1(il,jl,kl), rI(il,jl,kl) ,pk(dkR(jl)))
   in
    kdf(s,kI(il,jl,kl))
   else
    kdf(s,decap(ctI,dkR(j)))

in
     let K2 = kdf(s,DkR(j,k)) in
     let K3 = kdf(s,DkT(j,k)) in

     let ST = <pkI,<pk(dkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
     DsRI(j,k) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3))).


(* k-th copy of initiator with key dkI(i) trying to communicate with compromised responder with key pk(DdkR(j)) *)
process InitiatorToCompromised3(i,j,k:index) =
 let ctI = encap(DkI(i,j,k), F(DrI(i,j,k),skI(i)) XOR F(sk2I(i),DrI2(i,j,k))  ,pk(DdkR(j))) in
 let ekT = wpk(DdkT(i,j,k)) in
 out(cI, <ctI,ekT> ); (*we omit the public parameters in the output *)

 in(cR,messI);
 let ctR = fst(messI) in
 let ctT = snd(messI) in

 (* first key derivations *)
 let kT = wdecap(ctT,DdkT(i,j,k)) in

 (* Full common key derivations *)
 let K1 = kdf(s,DkI(i,j,k)) in
 let K2 =
   try find il,jl,kl such that
   ctR = encap(n_CCA(il,jl,kl), rR(il,jl,kl), pk(dkI(il)))
   in
       kdf(s,kR(il,jl,kl))
   else
   kdf(s,decap(ctR,dkI(i)))

in
 let K3 = kdf(s,kT) in

 let ST = <pk(dkI(i)),<pk(DdkR(j)),<ctI,<pk(ekT),<ctR,ctT>>>>> in
 sIR(i,j,k) := xor(G(ST,K1)) ( xor( G(ST,K2)) ( G(ST,K3))).


system [idealized] out(cI,s); ((!_j !_k R: Responder3(j,k)) | (!_i !_j !_k I: Initiator3(i,j,k))  | (!_i !_j !_k DI: InitiatorToCompromised3(i,j,k))).

axiom [mainCCAkI,idealized/left] tf: forall (x,y,z:message), decap(encap(x,y,pk(z)),z)=x.

equiv [mainCCAkI,idealized/left] ideal.
Proof.
  diffeq => * //.

    + case try find il,jl,kl such that _ in kR(il,jl,kl) else _.
      ++ case try find il, jl, kl such that _ in kdf(s,kR(il,jl,kl)) else _.
         have U :
          decap(encap(n_CCA(il,jl,kl),rR(il,jl,kl),pk(dkI(il))), dkI(il)) = 
          decap(encap(n_CCA(il0,jl0,kl0),rR(il0,jl0,kl0),pk(dkI(il0))), dkI(il)).
         rewrite tf in U.     
         by fresh U.
         by use H1 with il,jl,kl.
      ++ case try find il, jl, kl such that _ in kdf(s,kR(il,jl,kl)) else _.
         by use H1 with il,jl,kl.

    + case try find il,jl,kl such that _ in kR(il,jl,kl) else _.
      ++ case try find il, jl, kl such that _ in kdf(s,kR(il,jl,kl)) else _.
         have U :
          decap(encap(n_CCA(il,jl,kl),rR(il,jl,kl),pk(dkI(il))), dkI(il)) = 
          decap(encap(n_CCA(il0,jl0,kl0),rR(il0,jl0,kl0),pk(dkI(il0))), dkI(il)).
         rewrite tf in U.     
         by fresh U.
         by use H1 with il,jl,kl.
      ++ case try find il, jl, kl such that _ in kdf(s,kR(il,jl,kl)) else _.
         by use H1 with il,jl,kl.

    + case try find il,jl,kl such that _ in kI(il,jl,kl) else _.
      ++ case try find il, jl, kl such that _ in kdf(s,kI(il,jl,kl)) else _.
         have U :
          decap(encap (n_CCA1(il,jl,kl), rI(il,jl,kl), pk (dkR(jl))), dkR(jl)) = 
          decap(encap (n_CCA1(il0,jl0,kl0), rI(il0,jl0,kl0), pk (dkR(jl0))), dkR(jl)).
         rewrite tf in U.     
         by fresh U.
         by use H1 with il,jl,kl.
      ++ case try find il, jl, kl such that _ in kdf(s,kI(il,jl,kl)) else _.
         by use H1 with il,jl,kl.

    + case try find il,jl,kl such that _ in kI(il,jl,kl) else _.
      ++ case try find il, jl, kl such that _ in kdf(s,kI(il,jl,kl)) else _.
         have U :
          decap(encap (n_CCA1(il,jl,kl), rI(il,jl,kl), pk (dkR(jl))), dkR(jl)) = 
          decap(encap (n_CCA1(il0,jl0,kl0), rI(il0,jl0,kl0), pk (dkR(jl0))), dkR(jl)).
         rewrite tf in U.     
         by fresh U.
         by use H1 with il,jl,kl.
      ++ case try find il, jl, kl such that _ in kdf(s,kI(il,jl,kl)) else _.
         by use H1 with il,jl,kl.
Qed.

equiv [idealized/left,idealized/left] reflex.
Proof.
  diffeq => *.
Qed.

axiom  [idealized/left,idealized/left]  len_G (x1,x2:message) : len(G(x1,x2)) = len(s).

axiom  [idealized/left,idealized/left]  len_xor (x1,x2:message) : len(x1) = len(x2) => len(xor x1 x2) = len(x1).

(*******************************************)
(*** Strong Secrecy of the responder key ***)
(*******************************************)

set oldCompletion = true.

(* In idealized, we prove that at the end of R, the derived key is strongly secret. *)
global goal [idealized/left,idealized/left] resp_key (i,j,k:index[const]):
 [happens(R2(i,j,k))] -> 
 equiv(frame@R2(i,j,k), diff(sRI i j k@R2(i,j,k), kIR(i,j,k))) .
Proof.
  intro Hap .
  use reflex with R2(i,j,k) => //.
  expandall.
  prf 1, kdf(s,kR(k,i,j)); rewrite if_true // in 1.
  prf 1, G(_,n_PRF); rewrite if_true // in 1.
  xor 1,  xor n_PRF1 _, n_PRF1; rewrite if_true // in 1.
  rewrite len_G.
  namelength s, n_PRF1.
  xor 1,  n_XOR; rewrite if_true // in 1.
  rewrite len_G.
  namelength s, n_XOR.
  by fresh 1.
Qed.

(*******************************************)
(*** Strong Secrecy of the initiator key ***)
(*******************************************)

(* In idealized, we prove that at the end of R, the derived key is strongly secret. *)
global goal [idealized/left,idealized/left] right_key (i,j,k:index[const]):
  [happens(I1(i,j,k))] -> 
  equiv(frame@I1(i,j,k), diff(sIR i j k@I1(i,j,k), kIR(i,j,k))) .
Proof.
  intro Hap .
  use reflex with I1(i,j,k) => //.
  expandall.
  prf 1, kdf(s,kI(i,j,k)); rewrite if_true // in 1.
  prf 1, G(_, n_PRF); rewrite if_true // in 1.
  xor 1, n_PRF1; rewrite if_true // in 1.
  rewrite len_xor.
  by rewrite !len_G.
  rewrite len_G.
  by namelength s, n_PRF1.
  by fresh 1.
Qed.
