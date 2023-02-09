(*******************************************************************************

Generic 2xKEM - key exchange from Key encapsulation Mechanism (KEM)


[A] Boyd, Colin and Cliff, Yvonne and Nieto, Juan M. Gonzalez and Paterson, Kenneth G. One-round key exchange in the standard model.

# On KEMs

The protocol uses KEMS. In the paper, they are id based, which we abstract here.

The KEM are usally described with
(ek,dk) <- Keygen(r) returns an encryption key ek and a decryption key ek
(k,ct) <- Encap(r,ek) returns a session key k and its cyphertext ct
k <- Decap(ct,dk) returns k.

We abstract this with, pk, encap and decap function symbols, where
 * dk is a name, ek = pk(dk)
 * k is a name, ct=encap(k,r,pk(dk)).
 * decap(encap(k,r,pk(dk)),dk) = k

# Protocol description
We consider two parties I (initiator) and R (responder).
One KEM (Pk, Encap, DeCap) and two PRFs, Exct and Expd.
There is a public seed skex for Exct.


Static keys for party X := skX
Public keys for party X : pkX = pk(skX)


Initiator                                  Responder
new kI;
ctI := Encap(kI, rI  ,pk(skR))

                      --(I,ctI)->


                                         new kR;
                                         ctR := Encap(kR, rR , pk(skI))
                   I <--(R,ctR)-- R



kR := Decap(ctR,dkI)

                                         kI := Decap(ctI,dkI)

Final key deriviation:
kI2 := Exct(kI,skex)
kR2 := Exct(kR,skex)
s := (I,ctI,R,ctR)
KIR := expd(s,kI2) XOR expd(s,kR2)


# Model

We model an unbounded number of agents, each capable of initiating multiple sessions. The responder is willing to talk to anybody.


We prove for each agent that the computed key is real or random,
which implies the implicit authentication of the scheme: only the other trusted
party could potentially compute the key.


*******************************************************************************)
set postQuantumSound = true.

include Basic.

set oldCompletion = true.

hash exct

hash expd

(* public random key for exct *)

name skex : message

(* KEM *)

aenc encap,decap,pk

axiom [any] decap_encap (x,y,z : message) : decap(encap(x,y,pk(z)),z) = x.

(* long term key of I *)

name skI : index-> message

(* long term key of R *)
name skR : index->  message

(* session randomess of I *)
name kI : index * index * index -> message
name rI : index * index * index -> message

(* session randomess of R *)
name kR : index * index * index -> message
name rR : index * index * index -> message

(* session randomess of R for Dishonest cases*)
name DkR :  index * index -> message
name DrR :  index * index -> message


(* compromised long term key of R *)
name DskR : index->  message

(* session randomess of I talking to compromised *)
name DkI : index * index * index -> message
name DrI : index * index * index -> message


(* ideal keys *)
name ikIR : index * index * index -> message

mutable sIR(i,j,k:index) : message =  zero
mutable sRI(i,j,k:index) : message =  zero
mutable DsRI(j,k:index) : message =  zero
mutable DsIR(i,j,k:index) : message =  zero

abstract ok:message

channel cI
channel cR.


(* k-th copy of initiator with key skI(i) trying to communicate with responder with key pk(skR(j)) *)
process Initiator(i,j,k:index) =
  (* we only send an encapsulation to an honest peer, with what we assume to be a valid public key*)
 let ctI = encap(kI(i,j,k), rI(i,j,k) ,pk(skR(j))) in
 out(cI, ctI ); (* we omit the public parameters in the output *)

 in(cR,ctR);
 (* first key derivation *)
 (* common derivations *)
 let kI2 = exct(skex,kI(i,j,k)) in
 let kR2 = exct(skex,decap(ctR,skI(i)) ) in
 let s = <pk(skI(i)),<ctI,<pk(skR(j)),ctR>>> in
 sIR(i,j,k) :=  expd(s,kI2) XOR expd(s,kR2).

(* k-th copy of responder with key skR(j) *)
process Responder(j,k:index) =
   in(cR,pkI);
   in(cI, ctI);
   try find i such that pkI = pk(skI(i)) in
   (* to express security properties, we already split wether we recevied an honest or malicious key *)
     let ctR = encap(kR(i,j,k), rR(i,j,k), pk(skI(i))) in
     out(cR,ctR);

   (* common derivations *)
     let kI2 = exct(skex,decap(ctI,skR(j)) ) in
     let kR2 = exct(skex,kR(i,j,k)) in
     let s = <pk(skI(i)),<ctI,<pk(skR(j)),ctR>>> in
     sRI(j,k,i) :=  expd(s,kI2) XOR expd(s,kR2)
    else
     let DctR = encap(DkR(j,k), DrR(j,k), pkI) in
     out(cR,DctR);

   (* common derivations *)
     let DkI2 = exct(skex,decap(ctI,skR(j))) in
     let DkR2 = exct(skex,DkR(j,k)) in
     let Ds = <pkI,<ctI,<pk(skR(j)),DctR>>> in
     DsRI(j,k) :=  expd(Ds,DkI2) XOR expd(Ds,DkR2)

(* k-th copy of initiator with key skI(i) trying to communicate with compromised responder with key pk(DskR(j)) *)
process InitiatorToCompromised(i,j,k:index) =
  (* we only send an encapsulation to an honest peer, with what we assume to be a valid public key*)
 let ctI = encap(DkI(i,j,k), DrI(i,j,k) ,pk(DskR(j))) in
 out(cI, ctI ); (* we omit the public parameters in the output *)

 in(cR,ctR);
 (* first key derivation *)
 (* common derivations *)
 let kI2 = exct(skex,DkI(i,j,k)) in
 let kR2 = exct(skex,decap(ctR,skI(i)) ) in
 let s = <pk(skI(i)),<ctI,<pk(DskR(j)),ctR>>> in
 sIR(i,j,k) :=  expd(s,kI2) XOR expd(s,kR2).


system [main] out(cI,skex); ((!_j !_k R: Responder(j,k)) | (!_i !_j !_k I: Initiator(i,j,k))  | (!_i !_j !_k DI: InitiatorToCompromised(i,j,k))).


system mainCCAkR = [main/left] with gcca (il,jl,kl:index),  encap(kR(il,jl,kl), rR(il,jl,kl), pk(skI(il))).

system mainCCAkI = [mainCCAkR] with gcca (il,jl,kl:index),  encap(kI(il,jl,kl), rI(il,jl,kl) ,pk(skR(jl))).


(* After two transitivity, kR and kI only occurs in key position. We make it explicit in the idealized version of the protocol *)

(* k-th copy of initiator with key skI(i) trying to communicate with responder with key pk(skR(j)) *)
process Initiator2(i,j,k:index) =
  (* we only send an encapsulation to an honest peer, with what we assume to be a valid public key*)
 let ctI = encap(n_CCA1(i,j,k), rI(i,j,k) ,pk(skR(j))) in
 out(cI, ctI ); (* we omit the public parameters in the output *)

 in(cR,ctR);
 (* first key derivation *)
 (* common derivations *)
 let kI2 = exct(skex,kI(i,j,k)) in
 let kR2 =
     try find il,jl,kl such that
            ctR =  encap(n_CCA(il,jl,kl), rR(il,jl,kl), pk(skI(il))) in
             exct(skex,kR(il,jl,kl))
      else
       exct(skex,decap(ctR,skI(i)))
 in
 let s = <pk(skI(i)),<ctI,<pk(skR(j)),ctR>>> in
 sIR(i,j,k) :=  expd(s,kI2) XOR expd(s,kR2).

(* k-th copy of responder with key skR(j) *)
process Responder2(j,k:index) =
   in(cR,pkI);
   in(cI, ctI);
   try find i such that pkI = pk(skI(i)) in
   (* to express security properties, we already split wether we recevied an honest or malicious key *)
     let ctR = encap(n_CCA(i,j,k), rR(i,j,k), pk(skI(i))) in
     out(cR,ctR);
   (* first key derivation *)

   (* common derivations *)
     let kI2 =
     try find il,jl,kl such that
            ctI =  encap(n_CCA1(il,jl,kl), rI(il,jl,kl), pk(skR(jl))) in
             exct(skex,kI(il,jl,kl))
      else
       exct(skex,decap(ctI,skR(j)))

 in


     let kR2 = exct(skex,kR(i,j,k)) in
     let s = <pk(skI(i)),<ctI,<pk(skR(j)),ctR>>> in
     sRI(j,k,i) :=  expd(s,kI2) XOR expd(s,kR2)
    else
     let DctR = encap(DkR(j,k), DrR(j,k), pkI) in
     out(cR,DctR);

   (* common derivations *)
     let DkI2 =
     try find il,jl,kl such that
            ctI =  encap(n_CCA1(il,jl,kl), rI(il,jl,kl), pk(skR(jl))) in
             exct(skex,kI(il,jl,kl))
      else
       exct(skex,decap(ctI,skR(j)))
in

     let DkR2 = exct(skex,DkR(j,k)) in
     let Ds = <pkI,<ctI,<pk(skR(j)),DctR>>> in
     DsRI(j,k) :=  expd(Ds,DkI2) XOR expd(Ds,DkR2).

process InitiatorToCompromised2(i,j,k:index) =
  (* we only send an encapsulation to an honest peer, with what we assume to be a valid public key*)
 let ctI = encap(DkI(i,j,k), DrI(i,j,k) ,pk(DskR(j))) in
 out(cI, ctI ); (* we omit the public parameters in the output *)

 in(cR,ctR);
 (* first key derivation *)
 (* common derivations *)
 let kI2 = exct(skex,DkI(i,j,k)) in
 let kR2 =
     try find il,jl,kl such that
            ctR =  encap(n_CCA(il,jl,kl), rR(il,jl,kl), pk(skI(il))) in
             exct(skex,kR(il,jl,kl))
      else
       exct(skex,decap(ctR,skI(i)))
 in
 let s = <pk(skI(i)),<ctI,<pk(DskR(j)),ctR>>> in
 sIR(i,j,k) :=  expd(s,kI2) XOR expd(s,kR2).



system [idealized] out(cI,skex); ((!_j !_k R: Responder2(j,k)) | (!_i !_j !_k I: Initiator2(i,j,k))  | (!_i !_j !_k DI: InitiatorToCompromised2(i,j,k))).

axiom [mainCCAkI,idealized/left] tf: forall (x,y,z:message), decap(encap(x,y,pk(z)),z)=x.

(* We prove that the original game, after transitivity to mainCCAkI, is equivalent to idealized. *)
equiv [mainCCAkI,idealized/left] test.
Proof.

  diffeq => * //.

    + intro *.
      case try find il,jl,kl such that _ in kR(il,jl,kl) else _.
        ++ intro [il jl kl [A ->]].
           case try find il,jl,kl such that _ in exct(skex, kR(il,jl,kl)) else _.
             +++ intro [il0 jl0 kl0 [B ->]].
                 have U :
                 decap(encap(n_CCA(il,jl,kl),rR(il,jl,kl),pk(skI(il))), skI(il)) = 
                 decap(encap(n_CCA(il0,jl0,kl0),rR(il0,jl0,kl0),pk(skI(il0))), skI(il)).
                 auto.
                 rewrite !decap_encap in U. 
                 by fresh U.

             +++ intro [H1 _].
                 by use H1 with il,jl,kl.
        ++ intro [H1 _].
           case try find il,jl,kl such that _ in  exct(skex,kR(il,jl,kl)) else _.
           intro [il jl kl [A ->]].
           by use H1 with il,jl,kl.
           auto.

    + intro *.
      case try find il,jl,kl such that _ in kR(il,jl,kl) else _.
        ++ intro [il jl kl [A ->]].
           case try find il,jl,kl such that _ in exct(skex, kR(il,jl,kl)) else _.
             +++ intro [il0 jl0 kl0 [B ->]].
                 have U : decap(   encap(n_CCA(il,jl,kl),rR(il,jl,kl),pk(skI(il)))  , skI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rR(il0,jl0,kl0),pk(skI(il0))) , skI(il)).
                 auto.
                 rewrite !decap_encap in U. 
                 by fresh U.

             +++ intro [H1 _].
                 by use H1 with il,jl,kl.
        ++ intro [H1 _].
           case try find il,jl,kl such that _ in  exct(skex,kR(il,jl,kl)) else _.
           intro [il jl kl [A ->]].
           by use H1 with il,jl,kl.
           auto.

    + intro *.
      case try find il,jl,kl such that _ in  kI(il,jl,kl) else _.
        ++ intro [il jl kl [A ->]].
           case try find il,jl,kl such that _ in exct(skex, kI(il,jl,kl)) else _.
             +++ intro [il0 jl0 kl0 [B ->]].
                 have U : decap(   encap(n_CCA1(il,jl,kl),rI(il,jl,kl),pk(skR(jl)))  , skR(jl)) = decap(   encap(n_CCA1(il0,jl0,kl0),rI(il0,jl0,kl0),pk(skR(jl0))) , skR(jl)).
                 auto.
                 rewrite !decap_encap in U. 
                 by fresh U.

             +++ intro [H1 _].
                 by use H1 with il,jl,kl.
        ++ intro [H1 _].
           case try find il,jl,kl such that _ in  exct(skex,kI(il,jl,kl)) else _.
           intro [il jl kl [A ->]].
           by use H1 with il,jl,kl.
           auto.

    + intro *.
      case try find il,jl,kl such that _ in  kI(il,jl,kl) else _.
        ++ intro [il jl kl [A ->]].
           case try find il,jl,kl such that _ in exct(skex, kI(il,jl,kl)) else _.
             +++ intro [il0 jl0 kl0 [B ->]].
                 have U : decap(   encap(n_CCA1(il,jl,kl),rI(il,jl,kl),pk(skR(jl)))  , skR(jl)) = decap                 (   encap(n_CCA1(il0,jl0,kl0),rI(il0,jl0,kl0),pk(skR(jl0))) , skR(jl)).
                 auto.
                 rewrite !decap_encap in U. 
                 by fresh U.

             +++ intro [H1 _].
                 by use H1 with il,jl,kl.
         ++ intro [H1 _].
            case try find il,jl,kl such that _ in  exct(skex,kI(il,jl,kl)) else _.
            intro [il jl kl [A ->]].
            by use H1 with il,jl,kl.
            auto.
Qed.


equiv [idealized/left,idealized/left] reflex.
Proof.
  diffeq => *.
Qed.

axiom  [idealized/left,idealized/left] len_expd (x1,x2:message) : len(expd(x1,x2)) = len(skex).


(*******************************************)
(*** Strong Secrecy of the responder key ***)
(*******************************************)


(* In idealized, we prove that at the end of R, the derived key is strongly secret. *)
global goal [idealized/left,idealized/left] resp_key (i,j,k:index[const]):
  [happens(R2(i,j,k))] -> 
  equiv(frame@R2(i,j,k), diff(sRI i j k@R2(i,j,k), ikIR(i,j,k))).
Proof.
  intro Hap .
  use reflex with R2(i,j,k) => //.
  expandall.
  prf 1, exct(skex,kR(k,i,j)); rewrite if_true in 1.
  auto.
  prf 1; rewrite if_true in 1.
  auto.
  xor 1, xor _ _, n_PRF1. 
  rewrite len_expd.
  namelength n_PRF1, skex.
  intro Len.
  rewrite if_true in 1.
  auto.
  by fresh 1.
Qed.



(*******************************************)
(*** Strong Secrecy of the initiator key ***)
(*******************************************)


(* In idealized, we prove that at the end of R, the derived key is strongly secret. *)
global goal [idealized/left,idealized/left] right_key (i,j,k:index[const]):
  [happens(I1(i,j,k))] ->
  equiv(frame@I1(i,j,k), diff(sIR i j k@I1(i,j,k), ikIR(i,j,k))) .
Proof.
  intro Hap .
  use reflex with I1(i,j,k) => //.
  expandall.
  prf 1, exct(skex,kI(i,j,k)); rewrite if_true in 1.
  auto.
  prf 1, expd(<pk(skI(i)),
               <encap(n_CCA1(i,j,k),rI(i,j,k),pk(skR(j))),
                <pk(skR(j)),att(frame@pred(I1(i,j,k)))>>>,n_PRF) ; rewrite if_true in 1.
  auto.
  xor 1, n_PRF1.
  rewrite len_expd.
  namelength n_PRF1, skex.
  intro Len.
  rewrite if_true in 1.
  auto.
  by fresh 1.
Qed.


