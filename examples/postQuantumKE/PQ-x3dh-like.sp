(*******************************************************************************

PQ X3DH

[A] Keitaro Hashimoto,Shuichi Katsumata, Kris Kwiatkowski, Thomas Prest. An Efficient and Generic Construction for Signal’s Handshake (X3DH): Post-Quantum, State Leakage Secure, and Deniable.

The protocol is a X3DH like proposal, in the spirit of signal handshale.

# Protocol description

Each party i has two key pairs, one for kem and one for signatures:

 * eki = epk(vki)
 * dki = spk(ski)


Initiator(i)                        Responder(j)
new dkt
        pk(dkt)  -->     new kt; CT = encap(kt,pk(dkt))
                         new k; C = encap(k, eiki)
                         sid =  eki | ekj | pk(dkt) | C | CT
                         K1 = ext(k); K2=ext(Kt)
                         kj | k <- F(sid,K1) + F(sid,K2)
                         s <- sign(sid,skj)
                         c <- s + k
                         fkey = k
         <-- C,Ct,c
K = decap(C,vki)
KT = decp(Ct,dkt)
K1 = ext(k); K2=ext(Kt)
sid =  eki | ekj | pk(dkt) | C | CT
kj | k <- F(sid,K1) + F(sid,K2)
s <- c + k
verify(sid, dkj)
fkey =k


# Threat model

We consider the system
`((!_j !_i !_l R: Responder(j,i,l)) | (!_i !_j !_l I:Initiator(i,j,l)))`
Where Initiator(i,j,l) represent the l-th copy of an
initiator with key vkI(i) willing to talk to a responder with key vkR(j).

Initiator only sends to honest responder, but responder can answer to anybody.

We prove the authentication of the responder to the initiator, and the strong
secrecy of the keys.


*******************************************************************************)
set timeout = 10.
set postQuantumSound = true.

include Basic.

hash exct

(* public random key for exct *)

name skex : message

(* KEM *)

aenc encap,decap,epk

axiom [any] decap_encap (x,y,z : message) : decap(encap(x,y,epk(z)),z) = x.

(* sign *)

signature sign,checksign,spk

(* PRF *)

hash F1
hash F2

(* long term keys of I *)

name vkI : index ->  message
name skI : index ->  message

(* long term key of R *)
name vkR : index ->  message
name skR : index ->  message


(* session randomess of I *)
name dkt : index * index * index -> message.


(* session randomess of R *)
name kt  : index * index * index -> message
name K  : index * index * index -> message
name rkt : index * index * index -> message
name rk  : index * index * index -> message

(* session randomess of R with dishonnest I *)
name Dkt  : index * index -> message
name Dk   : index * index -> message
name Drkt : index * index -> message
name Drk  : index * index -> message

(* session randomess of I with dishonest R*)
name Ddkt : index * index * index -> message.

(* long term compromised keys *)
abstract DvkR : index ->  message.
abstract DskR : index ->  message.

(* key derivation storage *)
mutable sIR(i,j,k:index) : message = zero.
mutable sRI(i,j,k:index) : message = zero
mutable DsRI(j,k:index) : message = zero
mutable DsIR(i,j,k:index) : message =  zero.

(* ideal keys *)
name ikIR : index * index * index -> message.


abstract ok:message.

channel cI
channel cR.

(* Main protocol Model *)
(***********************)

(* Initiator vkI(i) who wants to talk to Responder epk(vkR(j)) *)
process Initiator(i,j,k:index) =
   out(cI, epk(dkt(i,j,k)) );

   in(cR,m);

   let KT = decap( fst(m),dkt(i,j,k) ) in

   let sid = < epk(vkI(i)), <epk(vkR(j)), <epk(dkt(i,j,k)) , <fst(snd(m)), fst(m)>>>> in
   let K1 = exct(skex,decap( fst(snd(m)), vkI(i) )) in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   if checksign(sid, ktilde XOR snd(snd(m)), spk(skR(j))) then
    FI :  sIR(i,j,k) := kj.

process Responder(j,k:index) =
(* Responder j who is willing to talk to initator i *)
   in(cR, epkI);
    in(cR, m);
  try find i such that epkI = epk(vkI(i)) in
   let CT = encap(kt(i,j,k), rkt(i,j,k), m) in
   let C = encap(K(i,j,k), rk(i,j,k), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,K(i,j,k)) in
   let K2 = exct(skex,kt(i,j,k)) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
    sRI(i,j,k) := kj;
   SR : out(cR,<CT,<C, ktilde XOR sign(sid, skR(j))   >>)
else
   let CT = encap(Dkt(j,k), Drkt(j,k), m) in
   let C = encap(Dk(j,k), Drk(j,k), epkI) in
   let sid = < epkI, <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,Dk(j,k)) in
   let K2 = exct(skex,Dkt(j,k)) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
    DsRI(j,k) := kj;
   DSR : out(cR,<CT,<C, ktilde XOR sign(sid, skR(j))   >>).

(* Initiator vkI(i) who wants to talk to Responder spk(DskR(j)), whose key is actually compromised *)
process InitiatorToCompromised(i,j,k:index) =
   out(cI, epk(Ddkt(i,j,k)) );

   in(cR,m);

   let KT = decap( fst(m),Ddkt(i,j,k) ) in

   let sid = < epk(vkI(i)), <epk(DvkR(j)), <epk(Ddkt(i,j,k)) , <fst(snd(m)), fst(m)>>>> in
   let K1 = exct(skex,decap( fst(snd(m)), vkI(i) )) in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   if checksign(sid, ktilde XOR snd(snd(m)), spk(DskR(j))) then
    DFI :  sIR(i,j,k) := kj.



system [main]  out(cI,skex); (
         (!_j !_k R: Responder(j,k)) 
       | (!_i !_j !_k I: Initiator(i,j,k))
       | (!_i !_j !_k DI: InitiatorToCompromised(i,j,k))
).


system mainCCAkR = [main/left] with gcca (il,jl,kl:index),  encap(K(il,jl,kl), rk(il,jl,kl), epk(vkI(il))).

(* System with hidden k(i,j,k). *)

(* Initiator vkI(i) who wants to talk to Responder spk(skR(j)) *)
process Initiator2(i,j,k:index) =
   out(cI, epk(dkt(i,j,k)) );

   in(cR,m);

   let KT = decap( fst(m),dkt(i,j,k) ) in

   let sid = < epk(vkI(i)), <epk(vkR(j)), <epk(dkt(i,j,k)) , <fst(snd(m)), fst(m)>>>> in
   let K1 =
    try find il,jl,kl such that
     fst(snd(m)) =  encap(n_CCA(il,jl,kl), rk(il,jl,kl), epk(vkI(il)))
     in
       exct(skex,K(il,jl,kl))
     else
       exct(skex,decap( fst(snd(m)), vkI(i) ))
   in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   if checksign(sid, ktilde XOR snd(snd(m)), spk(skR(j))) then
     FI:  sIR(i,j,k) := kj.

process Responder2(j,k:index) =
(* Responder j who is willing to talk to initator i *)
   in(cR, epkI);
    in(cR, m);
  try find i such that epkI = epk(vkI(i)) in
   let CT = encap(kt(i,j,k), rkt(i,j,k), m) in
   let C = encap(n_CCA(i,j,k), rk(i,j,k), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,K(i,j,k)) in
   let K2 = exct(skex,kt(i,j,k)) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
    sRI(i,j,k) := kj;
   SR : out(cR,<CT,<C, ktilde XOR sign(sid, skR(j))   >>)
else
   let CT = encap(Dkt(j,k), Drkt(j,k), m) in
   let C = encap(Dk(j,k), Drk(j,k), epkI) in
   let sid = < epkI, <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,Dk(j,k)) in
   let K2 = exct(skex,Dkt(j,k)) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
    DsRI(j,k) := kj;
   DSR : out(cR,<CT,<C, ktilde XOR sign(sid, skR(j))   >>)
.
process InitiatorToCompromised2(i,j,k:index) =
   out(cI, epk(Ddkt(i,j,k)) );

   in(cR,m);

   let KT = decap( fst(m),Ddkt(i,j,k) ) in

   let sid = < epk(vkI(i)), <epk(DvkR(j)), <epk(Ddkt(i,j,k)) , <fst(snd(m)), fst(m)>>>> in
   let K1 =
    try find il,jl,kl such that
     fst(snd(m)) =  encap(n_CCA(il,jl,kl), rk(il,jl,kl), epk(vkI(il)))
     in
       exct(skex,K(il,jl,kl))
     else
       exct(skex,decap( fst(snd(m)), vkI(i) ))
   in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   if checksign(sid, ktilde XOR snd(snd(m)), spk(DskR(j))) then
    DFI :  sIR(i,j,k) := kj.

system [idealized]  out(cI,skex); ((!_j !_k R: Responder2(j,k)) | (!_i !_j !_k I: Initiator2(i,j,k)) | (!_i !_j !_k I: InitiatorToCompromised2(i,j,k))).

axiom [mainCCAkR,idealized/left] tf: forall (x,y,z:message), decap(encap(x,y,epk(z)),z)=x.

(* We prove that the original game, after transitivity to mainCCAkI, is equivalent to idealized. *)
equiv [mainCCAkR,idealized/left] test.
Proof.
  diffeq => * //.
    + intro *.
      case try find il,jl,kl such that _ in K(il,jl,kl) else _.
        - intro [il jl kl [Eq ->]].
          case try find il,jl,kl such that _ in exct(skex, K(il,jl,kl)) else _.
            * intro [il0 jl0 kl0 [Eq2 ->]].
              assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).
              auto.
              rewrite !decap_encap in Meq. 
              by fresh Meq.

            * intro [Abs _].
              by use Abs with il,jl,kl.

        - case try find il,jl,kl such that _ in  exct(skex,K(il,jl,kl)) else _.
          * intro [il jl kl Ex] [Abs _].
            use Abs with il,jl,kl => //. 
          * auto.

    + intro *.
      case try find il,jl,kl such that _ in K(il,jl,kl) else _.
        - intro [il jl kl [Eq ->]].
          case try find il,jl,kl such that _ in exct(skex, K(il,jl,kl)) else _.
            * intro [il0 jl0 kl0 [Eq2 ->]].
              assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).
              auto.
              rewrite !decap_encap in Meq. 
              by fresh Meq.

            * intro [Abs _].
              by use Abs with il,jl,kl.

        - case try find il,jl,kl such that _ in  exct(skex,K(il,jl,kl)) else _.
          * intro [il jl kl Ex] [Abs _].
            by use Abs with il,jl,kl.
          * auto.

    + intro *.
      case try find il,jl,kl such that _ in K(il,jl,kl) else _.
        - intro [il jl kl [Eq ->]].
          case try find il,jl,kl such that _ in exct(skex, K(il,jl,kl)) else _.
            * intro [il0 jl0 kl0 [Eq2 ->]].
              assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).
              auto.
              rewrite !decap_encap in Meq. 
              by fresh Meq.

            * intro [Abs _].
              by use Abs with il,jl,kl.

          - case try find il,jl,kl such that _ in  exct(skex,K(il,jl,kl)) else _.
            * intro [il jl kl Ex] [Abs _].
              by use Abs with il,jl,kl.
            * intro A B; clear A B; auto.

    + intro *.
      case try find il,jl,kl such that _ in K(il,jl,kl) else _.
        - intro [il jl kl [Eq ->]].
          case try find il,jl,kl such that _ in exct(skex, K(il,jl,kl)) else _.
            * intro [il0 jl0 kl0 [Eq2 ->]].
              assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).
              auto.
              rewrite !decap_encap in Meq. 
              by fresh Meq.

            * intro [Abs _].
              by use Abs with il,jl,kl.

        - case try find il,jl,kl such that _ in  exct(skex,K(il,jl,kl)) else _.
          intro [il jl kl Ex] [Abs _].
          by use Abs with il,jl,kl.
          auto.

    + intro *.
      case try find il,jl,kl such that _ in K(il,jl,kl) else _.
        - intro [il jl kl [Eq ->]].
          case try find il,jl,kl such that _ in exct(skex, K(il,jl,kl)) else _.
            * intro [il0 jl0 kl0 [Eq2 ->]].
              assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).
              auto.
              rewrite !decap_encap in Meq. 
              by fresh Meq.
              
            * intro [Abs _].
              by use Abs with il,jl,kl.

        - case try find il,jl,kl such that _ in  exct(skex,K(il,jl,kl)) else _.
          intro [il jl kl Ex] [Abs _].
          by use Abs with il,jl,kl.
          auto.

    + intro *.
      case try find il,jl,kl such that _ in K(il,jl,kl) else _.
        - intro [il jl kl [Eq ->]].
          case try find il,jl,kl such that _ in exct(skex, K(il,jl,kl)) else _.
            * intro [il0 jl0 kl0 [Eq2 ->]].
              assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).
              auto.
              rewrite !decap_encap in Meq. 
              by fresh Meq.

            * intro [Abs _].
              by use Abs with il,jl,kl.

          - case try find il,jl,kl such that _ in  exct(skex,K(il,jl,kl)) else _.
            intro [il jl kl Ex] [Abs _].
            by use Abs with il,jl,kl.
            auto.
Qed.

system idealized2 = [idealized/left] with gprf (iv,jv,kv:index),  exct(skex,K(iv,jv,kv)).

(* System with idealized key. *)
(******************************)

(* Initiator vkI(i) who wants to talk to Responder spk(skR(j)) *)
process Initiator3(i,j,k:index) =
   out(cI, epk(dkt(i,j,k)) );

   in(cR,m);

   let KT = decap( fst(m),dkt(i,j,k) ) in

   let sid = < epk(vkI(i)), <epk(vkR(j)), <epk(dkt(i,j,k)) , <fst(snd(m)), fst(m)>>>> in
   let FK1 =
    try find il,jl,kl such that
     fst(snd(m)) =  encap(n_CCA(il,jl,kl), rk(il,jl,kl), epk(vkI(il)))
     in
       F1(sid,n_PRF(il,jl,kl))
     else
       F1(sid,exct(skex,decap( fst(snd(m)), vkI(i) )))
   in
   let FK2 =
    try find il,jl,kl such that
     fst(snd(m)) =  encap(n_CCA(il,jl,kl), rk(il,jl,kl), epk(vkI(il)))
     in
       F2(sid,n_PRF(il,jl,kl))
     else
       F2(sid,exct(skex,decap( fst(snd(m)), vkI(i) )))
   in
   let K2 = exct(skex,KT) in
   let kj = FK1 XOR F1(sid,K2) in
   let ktilde = FK2 XOR F2(sid,K2) in
   if checksign(sid, ktilde XOR snd(snd(m)), spk(skR(j))) then
     FI:  sIR(i,j,k) := kj.

process Responder3(j,k:index) =
(* Responder j who is willing to talk to initator i *)
   in(cR, epkI);
    in(cR, m);
  try find i such that epkI = epk(vkI(i)) in
   let CT = encap(kt(i,j,k), rkt(i,j,k), m) in
   let C = encap(n_CCA(i,j,k), rk(i,j,k), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in

(*   let K1 = n_PRF(i,j,k) in *)

   let K2 = exct(skex,kt(i,j,k)) in
   let kj = F1(sid, n_PRF(i,j,k)) XOR F1(sid,K2) in
   let ktilde = F2(sid, n_PRF(i,j,k)) XOR F2(sid,K2) in
    sRI(i,j,k) := kj;
   SR : out(cR,<CT,<C, ktilde XOR sign(sid, skR(j))   >>)
else
   let CT = encap(Dkt(j,k), Drkt(j,k), m) in
   let C = encap(Dk(j,k), Drk(j,k), epkI) in
   let sid = < epkI, <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,Dk(j,k)) in
   let K2 = exct(skex,Dkt(j,k)) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
    DsRI(j,k) := kj;
   DSR : out(cR,<CT,<C, ktilde XOR sign(sid, skR(j))   >>)
.

process InitiatorToCompromised3(i,j,k:index) =
   out(cI, epk(Ddkt(i,j,k)) );

   in(cR,m);

   let KT = decap( fst(m),Ddkt(i,j,k) ) in

   let sid = < epk(vkI(i)), <epk(DvkR(j)), <epk(Ddkt(i,j,k)) , <fst(snd(m)), fst(m)>>>> in
   let FK1 =
    try find il,jl,kl such that
     fst(snd(m)) =  encap(n_CCA(il,jl,kl), rk(il,jl,kl), epk(vkI(il)))
     in
       F1(sid,n_PRF(il,jl,kl))
     else
       F1(sid,exct(skex,decap( fst(snd(m)), vkI(i) )))
   in
   let FK2 =
    try find il,jl,kl such that
     fst(snd(m)) =  encap(n_CCA(il,jl,kl), rk(il,jl,kl), epk(vkI(il)))
     in
       F2(sid,n_PRF(il,jl,kl))
     else
       F2(sid,exct(skex,decap( fst(snd(m)), vkI(i) )))
   in
   let K2 = exct(skex,KT) in
   let kj = FK1 XOR F1(sid,K2) in
   let ktilde = FK2 XOR F2(sid,K2) in
   if checksign(sid, ktilde XOR snd(snd(m)), spk(DskR(j))) then
     FI:  sIR(i,j,k) := kj.



system [idealized3]  out(cI,skex); ((!_j !_k R: Responder3(j,k)) | (!_i !_j !_k I: Initiator3(i,j,k)) | (!_i !_j !_k I: InitiatorToCompromised3(i,j,k))).

axiom [idealized3/left,idealized2] ifte (i,j,k:index): att(frame@pred(FI(i,j,k))) =  att(frame@pred(I1(i,j,k))).

axiom [idealized3/left,idealized2] ifteD (i,j,k:index): att(frame@pred(DFI(i,j,k))) =  att(frame@pred(DI1(i,j,k))).


goal  [idealized3/left,idealized2] trans_eq (i,j,k:index):
xor(try find il,jl,kl such that
      fst(snd(att(frame@pred(I1(i,j,k))))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in
      F2(<epk(vkI(i)),
          <epk(vkR(j)),
           <epk(dkt(i,j,k)),
            <fst(snd(att(frame@pred(I1(i,j,k))))),
             fst(att(frame@pred(I1(i,j,k))))>>>>,n_PRF(il,jl,kl))
    else
      F2(<epk(vkI(i)),
          <epk(vkR(j)),
           <epk(dkt(i,j,k)),
            <fst(snd(att(frame@pred(I1(i,j,k))))),
             fst(att(frame@pred(I1(i,j,k))))>>>>,
      exct(skex,decap(fst(snd(att(frame@pred(I1(i,j,k))))),vkI(i)))))
(F2(<epk(vkI(i)),
    <epk(vkR(j)),
     <epk(dkt(i,j,k)),
      <fst(snd(att(frame@pred(I1(i,j,k))))),fst(att(frame@pred(I1(i,j,k))))>>>>,
exct(skex,decap(fst(att(frame@pred(I1(i,j,k)))),dkt(i,j,k))))) =
xor(F2(<epk(vkI(i)),
        <epk(vkR(j)),
         <epk(dkt(i,j,k)),
          <fst(snd(att(frame@pred(I1(i,j,k))))),
           fst(att(frame@pred(I1(i,j,k))))>>>>,
    try find il,jl,kl such that
      fst(snd(att(frame@pred(I1(i,j,k))))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in
      try find iv,jv,kv such that
        (skex = skex && (il = iv && jl = jv && kl = kv))
      in n_PRF(iv,jv,kv) else exct(skex,K(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(I1(i,j,k))))),vkI(i)))))
(F2(<epk(vkI(i)),
    <epk(vkR(j)),
     <epk(dkt(i,j,k)),
      <fst(snd(att(frame@pred(I1(i,j,k))))),fst(att(frame@pred(I1(i,j,k))))>>>>,
exct(skex,decap(fst(att(frame@pred(I1(i,j,k)))),dkt(i,j,k))))).
Proof.

  case try find il,jl,kl such that
        fst(snd(att(frame@pred(I1(i,j,k))))) =
        encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
      in
        F2(<epk(vkI(i)),
            <epk(vkR(j)),
             <epk(dkt(i,j,k)),
              <fst(snd(att(frame@pred(I1(i,j,k))))),
               fst(att(frame@pred(I1(i,j,k))))>>>>,n_PRF(il,jl,kl))
      else _.
    + intro [il jl kl [U ->]]. 
      case   try find il,jl,kl such that
            fst(snd(att(frame@pred(I1(i,j,k))))) =
            encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
          in
       _
          else exct(skex,decap(fst(snd(att(frame@pred(I1(i,j,k))))),vkI(i))).
        ++ intro [il0 jl0 kl0 [V ->]]. 
           case  try find iv,jv,kv such that
                 (skex = skex && (il0 = iv && jl0 = jv && kl0 = kv))
                 in n_PRF(iv,jv,kv) else exct(skex,K(il0,jl0,kl0)).
           +++ intro [??? [[_ [_ _ _]] ->]].
               assert decap( encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
               decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))), vkI(il)).
               auto.
              rewrite !decap_encap in Meq. 
              by fresh Meq.

          +++ intro [Abs _].
              by use Abs with il0,jl0,kl0.
        ++ intro [Abs _].
           by use Abs with il,jl,kl.

     + intro [Abs M].
       case   try find il,jl,kl such that
             fst(snd(att(frame@pred(I1(i,j,k))))) =
             encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
           in
             try find iv,jv,kv such that
               (skex = skex && (il = iv && jl = jv && kl = kv))
             in n_PRF(iv,jv,kv) else exct(skex,K(il,jl,kl))
           else exct(skex,decap(fst(snd(att(frame@pred(I1(i,j,k))))),vkI(i))).
       ++ intro [il jl kl [_ ->]]. 
          by use Abs with il,jl,kl.
       ++ intro [A B]; clear A M Abs.
          rewrite B. 
          congruence. 
Qed.


goal  [idealized3/left,idealized2] trans_eqD (i,j,k:index):
xor(try find il,jl,kl such that
      (fst(snd(att(frame@pred(DI1(i,j,k))))) =
       encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))))
    in
      F2(<epk(vkI(i)),
          <epk(DvkR(j)),
           <epk(Ddkt(i,j,k)),
            <fst(snd(att(frame@pred(DI1(i,j,k))))),
             fst(att(frame@pred(DI1(i,j,k))))>>>>,n_PRF(il,jl,kl))
    else
      F2(<epk(vkI(i)),
          <epk(DvkR(j)),
           <epk(Ddkt(i,j,k)),
            <fst(snd(att(frame@pred(DI1(i,j,k))))),
             fst(att(frame@pred(DI1(i,j,k))))>>>>,
      exct(skex,decap(fst(snd(att(frame@pred(DI1(i,j,k))))),vkI(i)))))
(F2(<epk(vkI(i)),
    <epk(DvkR(j)),
     <epk(Ddkt(i,j,k)),
      <fst(snd(att(frame@pred(DI1(i,j,k))))),fst(att(frame@pred(DI1(i,j,k))))>>>>,
exct(skex,decap(fst(att(frame@pred(DI1(i,j,k)))),Ddkt(i,j,k))))) =
xor(F2(<epk(vkI(i)),
        <epk(DvkR(j)),
         <epk(Ddkt(i,j,k)),
          <fst(snd(att(frame@pred(DI1(i,j,k))))),
           fst(att(frame@pred(DI1(i,j,k))))>>>>,
    try find il,jl,kl such that
      (fst(snd(att(frame@pred(DI1(i,j,k))))) =
       encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))))
    in
      try find iv,jv,kv such that
        ((skex = skex) && ((il = iv) && (jl = jv) && (kl = kv)))
      in n_PRF(iv,jv,kv) else exct(skex,K(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(DI1(i,j,k))))),vkI(i)))))
(F2(<epk(vkI(i)),
    <epk(DvkR(j)),
     <epk(Ddkt(i,j,k)),
      <fst(snd(att(frame@pred(DI1(i,j,k))))),fst(att(frame@pred(DI1(i,j,k))))>>>>,
exct(skex,decap(fst(att(frame@pred(DI1(i,j,k)))),Ddkt(i,j,k))))).

Proof.

  case try find il,jl,kl such that
        fst(snd(att(frame@pred(DI1(i,j,k))))) =
        encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
      in
        F2(<epk(vkI(i)),
            <epk(DvkR(j)),
             <epk(Ddkt(i,j,k)),
              <fst(snd(att(frame@pred(DI1(i,j,k))))),
               fst(att(frame@pred(DI1(i,j,k))))>>>>,n_PRF(il,jl,kl))
      else _.
   + intro [il jl kl [_ ->]]. 
     case   try find il,jl,kl such that
           fst(snd(att(frame@pred(DI1(i,j,k))))) =
           encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
         in
      _
         else exct(skex,decap(fst(snd(att(frame@pred(DI1(i,j,k))))),vkI(i))).
       ++ intro [il0 jl0 kl0 [_ ->]]. 
          case   try find iv,jv,kv such that
                (skex = skex && (il0 = iv && jl0 = jv && kl0 = kv))
              in n_PRF(iv,jv,kv) else exct(skex,K(il0,jl0,kl0)).
            +++ intro [??? [Eq2 ->]].
                assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).
                auto.
                rewrite !decap_encap in Meq. 
                by fresh Meq.

            +++ intro [Abs _].
                by use Abs with il0,jl0,kl0.
        ++ intro [Abs _].
          by use Abs with il,jl,kl.

    + intro [Abs M].
      case   try find il,jl,kl such that
            fst(snd(att(frame@pred(DI1(i,j,k))))) =
            encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
          in
            _
          else exct(skex,decap(fst(snd(att(frame@pred(DI1(i,j,k))))),vkI(i))).
      intro [il jl kl [_ ->]]. 
      by use Abs with il,jl,kl.
      auto.
Qed.


axiom [idealized3/left,idealized2]  fasign :
  forall (s1,s2,m1,m2,k:message),
  s1=s2 => checksign(m1,s1,k) => checksign(m2,s2,k) => m1 = m2.


goal  [idealized3/left,idealized2] trans_eq2 (i,j,k:index):
xor(try find il,jl,kl such that
      fst(snd(att(frame@pred(FI(i,j,k))))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in
      F1(<epk(vkI(i)),
          <epk(vkR(j)),
           <epk(dkt(i,j,k)),
            <fst(snd(att(frame@pred(FI(i,j,k))))),
             fst(att(frame@pred(FI(i,j,k))))>>>>,n_PRF(il,jl,kl))
    else
      F1(<epk(vkI(i)),
          <epk(vkR(j)),
           <epk(dkt(i,j,k)),
            <fst(snd(att(frame@pred(FI(i,j,k))))),
             fst(att(frame@pred(FI(i,j,k))))>>>>,
      exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i)))))
(F1(<epk(vkI(i)),
    <epk(vkR(j)),
     <epk(dkt(i,j,k)),
      <fst(snd(att(frame@pred(FI(i,j,k))))),fst(att(frame@pred(FI(i,j,k))))>>>>,
exct(skex,decap(fst(att(frame@pred(FI(i,j,k)))),dkt(i,j,k))))) =
xor(F1(<epk(vkI(i)),
        <epk(vkR(j)),
         <epk(dkt(i,j,k)),
          <fst(snd(att(frame@pred(FI(i,j,k))))),
           fst(att(frame@pred(FI(i,j,k))))>>>>,
    try find il,jl,kl such that
      fst(snd(att(frame@pred(FI(i,j,k))))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in
      try find iv,jv,kv such that
        (skex = skex && (il = iv && jl = jv && kl = kv))
      in n_PRF(iv,jv,kv) else exct(skex,K(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i)))))
(F1(<epk(vkI(i)),
    <epk(vkR(j)),
     <epk(dkt(i,j,k)),
      <fst(snd(att(frame@pred(FI(i,j,k))))),fst(att(frame@pred(FI(i,j,k))))>>>>,
exct(skex,decap(fst(att(frame@pred(FI(i,j,k)))),dkt(i,j,k))))).
Proof.

  case try find il,jl,kl such that
          fst(snd(att(frame@pred(FI(i,j,k))))) =
          encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
        in
          F1(<epk(vkI(i)),
              <epk(vkR(j)),
               <epk(dkt(i,j,k)),
                <fst(snd(att(frame@pred(FI(i,j,k))))),
                 fst(att(frame@pred(FI(i,j,k))))>>>>,n_PRF(il,jl,kl))
        else
          F1(<epk(vkI(i)),
              <epk(vkR(j)),
               <epk(dkt(i,j,k)),
                <fst(snd(att(frame@pred(FI(i,j,k))))),
                 fst(att(frame@pred(FI(i,j,k))))>>>>,
          exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i)))).
    + intro [il jl kl [_ ->]]. 
      case  try find il,jl,kl such that
          fst(snd(att(frame@pred(FI(i,j,k))))) =
          encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
             in
             try find iv,jv,kv such that
             (skex = skex && (il = iv && jl = jv && kl = kv))
               in n_PRF(iv,jv,kv) else exct(skex,K(il,jl,kl))
            else exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i))).
        ++ intro [il0 jl0 kl0 [_ ->]]. 
           case  try find iv,jv,kv such that
                 (skex = skex && (il0 = iv && jl0 = jv && kl0 = kv))
               in n_PRF(iv,jv,kv) else exct(skex,K(il0,jl0,kl0)).
             +++ intro [iv jv kv [_ ->]]. 
                 assert decap( encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
                 decap(   encap(n_CCA(iv,jv,kv),rk(iv,jv,kv),epk(vkI(iv))), vkI(il)).
                 auto.
                 rewrite !decap_encap in Meq. 
                 by fresh Meq.

             +++ intro [Abs _].
                 by use Abs with il0,jl0,kl0.

         ++ intro [Abs _].
            by use Abs with il,jl,kl.

     + intro [Abs M].
       case     try find il,jl,kl such that
             fst(snd(att(frame@pred(FI(i,j,k))))) =
             encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
           in
             try find iv,jv,kv such that
               (skex = skex && (il = iv && jl = jv && kl = kv))
             in n_PRF(iv,jv,kv) else exct(skex,K(il,jl,kl))
           else exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i))).
       ++ intro [il jl kl [_ ->]]. 
          by use Abs with il,jl,kl.
       ++ intro [A B]. 
          rewrite B M. 
          clear A B M Abs. 
          congruence.
Qed.



goal  [idealized3/left,idealized2] trans_eq2D (i,j,k:index):
xor(try find il,jl,kl such that
      (fst(snd(att(frame@pred(DFI(i,j,k))))) =
       encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))))
    in
      F1(<epk(vkI(i)),
          <epk(DvkR(j)),
           <epk(Ddkt(i,j,k)),
            <fst(snd(att(frame@pred(DFI(i,j,k))))),
             fst(att(frame@pred(DFI(i,j,k))))>>>>,n_PRF(il,jl,kl))
    else
      F1(<epk(vkI(i)),
          <epk(DvkR(j)),
           <epk(Ddkt(i,j,k)),
            <fst(snd(att(frame@pred(DFI(i,j,k))))),
             fst(att(frame@pred(DFI(i,j,k))))>>>>,
      exct(skex,decap(fst(snd(att(frame@pred(DFI(i,j,k))))),vkI(i)))))
(F1(<epk(vkI(i)),
    <epk(DvkR(j)),
     <epk(Ddkt(i,j,k)),
      <fst(snd(att(frame@pred(DFI(i,j,k))))),fst(att(frame@pred(DFI(i,j,k))))>>>>,
exct(skex,decap(fst(att(frame@pred(DFI(i,j,k)))),Ddkt(i,j,k))))) =
xor(F1(<epk(vkI(i)),
        <epk(DvkR(j)),
         <epk(Ddkt(i,j,k)),
          <fst(snd(att(frame@pred(DFI(i,j,k))))),
           fst(att(frame@pred(DFI(i,j,k))))>>>>,
    try find il,jl,kl such that
      (fst(snd(att(frame@pred(DFI(i,j,k))))) =
       encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))))
    in
      try find iv,jv,kv such that
        ((skex = skex) && ((il = iv) && (jl = jv) && (kl = kv)))
      in n_PRF(iv,jv,kv) else exct(skex,K(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(DFI(i,j,k))))),vkI(i)))))
(F1(<epk(vkI(i)),
    <epk(DvkR(j)),
     <epk(Ddkt(i,j,k)),
      <fst(snd(att(frame@pred(DFI(i,j,k))))),fst(att(frame@pred(DFI(i,j,k))))>>>>,
exct(skex,decap(fst(att(frame@pred(DFI(i,j,k)))),Ddkt(i,j,k))))).
Proof.

  case try find il,jl,kl such that
        fst(snd(att(frame@pred(DFI(i,j,k))))) =
        encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
      in
     _
      else
        F1(<epk(vkI(i)),
            <epk(DvkR(j)),
             <epk(Ddkt(i,j,k)),
              <fst(snd(att(frame@pred(DFI(i,j,k))))),
               fst(att(frame@pred(DFI(i,j,k))))>>>>,
        exct(skex,decap(fst(snd(att(frame@pred(DFI(i,j,k))))),vkI(i)))).
    + intro [il jl kl [_ ->]].
      case  try find il,jl,kl such that
            fst(snd(att(frame@pred(DFI(i,j,k))))) =
            encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
          in
         _
          else exct(skex,decap(fst(snd(att(frame@pred(DFI(i,j,k))))),vkI(i))).
        ++ intro [il0 jl0 kl0 [_ ->]].
           case  try find iv,jv,kv such that
                 (skex = skex && (il0 = iv && jl0 = jv && kl0 = kv))
               in n_PRF(iv,jv,kv) else exct(skex,K(il0,jl0,kl0)).
             +++ intro [iv jv kv [_ ->]].
                 assert decap( encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
                 decap(   encap(n_CCA(iv,jv,kv),rk(iv,jv,kv),epk(vkI(iv))), vkI(il)).
                 auto.
                 rewrite !decap_encap in Meq. 
                 by fresh Meq.

             +++ intro [Abs _].
                 by use Abs with il0,jl0,kl0.

         ++ intro [Abs _].
            by use Abs with il,jl,kl.

      + intro [Abs _].
        case     try find il,jl,kl such that
              fst(snd(att(frame@pred(DFI(i,j,k))))) =
              encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
            in
             _
            else exct(skex,decap(fst(snd(att(frame@pred(DFI(i,j,k))))),vkI(i))).
        intro [il jl kl [_ ->]].
        by use Abs with il,jl,kl.
        auto.
Qed.


equiv [idealized3/left,idealized2] transitivity.
Proof.
  diffeq => * //.
  + intro *.
    by use trans_eqD with i,j,k.

  + intro *.
    by use trans_eq2D with i,j,k.

  + intro *.
    use ifteD with i,j,k.
    use trans_eqD with i,j,k.
    rewrite -Meq in Meq0.
    rewrite -Meq0.
    auto.

  + intro *.
    by use trans_eq with i,j,k.

  + intro *.
    by use trans_eq2 with i,j,k.

  + intro *.
    use ifte with i,j,k.
    use trans_eq with i,j,k.
    rewrite -Meq in Meq0.
    rewrite -Meq0.
    auto.

  + intro *.
    case  try find iv,jv,kv such that (skex = skex && (i = iv && j = jv && k = kv))
        in n_PRF(iv,jv,kv) else exct(skex,K(i,j,k)).
      ++ intro [iv jv kv [_ ->]].
         auto.
      ++ intro [Abs _].
         by use Abs with i,j,k.

  + intro *.
    case    try find iv,jv,kv such that (skex = skex && (i = iv && j = jv && k = kv))
        in n_PRF(iv,jv,kv) else exct(skex,K(i,j,k)).
      ++ intro [iv jv kv [_ ->]].
         auto.

      ++ intro [Abs _].
         by use Abs with i,j,k.
Qed.

axiom [idealized3] uniqepk : forall (m1,m2:message), epk(m1) =epk(m2) => m1=m2.

axiom [idealized3] sufcma :
forall (m,s,sk:message), checksign(m,s,spk(sk)) => s = sign(m,sk).

axiom [idealized3] xorconcel : forall (m1,m2,m3:message) m1=m2 => 
  xor m1 (xor m2 m3) = m3.

axiom [idealized3] rcheck :
 forall (m1,m2,sk:message), m1=m2 => checksign(m1, sign(m2,sk),spk(sk)).

goal [idealized3/left] auth :  forall (i,j,l:index) ,
   happens(FI(i,j,l)) =>
        exec@FI(i,j,l) =>
        exists (k:index),
          I(i,j,l) < FI(i,j,l) &&
          SR(j,k,i) < FI(i,j,l) &&
          input@SR(j,k,i) =  output@I(i,j,l) &&
          fst(output@SR(j,k,i)) = fst(input@FI(i,j,l)) &&
          fst(snd(output@SR(j,k,i))) = fst(snd(input@FI(i,j,l))) &&
          snd(snd(output@SR(j,k,i))) = snd(snd(input@FI(i,j,l)))
.
Proof.
  intro i j l.
  intro Hap Exec.
  expand exec.
  expand cond.
  destruct Exec as [_ EUF].

  euf EUF.
    + intro [k i0 [Ord Meq]].
      assert ( SR(j,k,i0) <= FI(i,j,l) || SR(j,k,i0) < FI(i,j,l)) <=>  SR(j,k,i0) < FI(i,j,l).
        ++ split.
           intro H.
           by case H.
           auto.
        ++ destruct H.
           use H => //.
           use uniqepk with vkI(i),vkI(i0) => //.
           exists k.
           depends I(i,j,l), FI(i,j,l) => //.
           intro OrdIFI.
           simpl.
           use sufcma with sid10(i,j,l)@FI(i,j,l), (xor(ktilde10(i,j,l)@FI(i,j,l)) (snd(snd(input@FI(i,j,l)))))  ,  skR(j); try auto .
           expand output.

           use xorconcel with ktilde8(j,k,i)@SR(j,k,i), ktilde8(j,k,i)@SR(j,k,i), sign(sid8(j,k,i)@SR(j,k,i),skR(j)) => //.
           rewrite Meq in Meq0.
           rewrite -Meq0.
           expand sid10,sid8, C4,CT4.
           simpl.
           assert ktilde8(j,k,i)@SR(j,k,i)=ktilde10(i,j,l)@FI(i,j,l).
             +++ expand ktilde8, ktilde10, FK2.
                 case  try find il,jl,kl such that
                      _
                     in F2(sid10(i,j,l)@FI(i,j,l),n_PRF(il,jl,kl))
                     else
                       F2(sid10(i,j,l)@FI(i,j,l),
                       exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i)))).
                 intro [il jl kl [ _ ->]].
                 have U :
                 decap(encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
                 decap(encap(n_CCA(i,j,k),rk(i,j,k),epk(vkI(i))), vkI(il)).
                 auto.
                 rewrite !decap_encap in U. 
                 by fresh U.

                 intro [Abs _].
                 by use Abs with i,j,k.
             +++ rewrite Meq2.
                 by use xorconcel with ktilde10(i,j,l)@FI(i,j,l), ktilde10(i,j,l)@FI(i,j,l),snd(snd(input@FI(i,j,l))) .

    + intro [k [Ord Eqsid]].
      executable pred(FI(i,j,l)) => //.
      intro Exec.
      use Exec with DSR(j,k) => //.
      assert happens(DSR(j,k)); [1:auto].
      expand  exec@DSR(j,k).
      expand cond.
      destruct H as [_ Conc].
      by use Conc with i.
Qed.
(* As I1 is the converse of FI, we also have freely that *)

global axiom [idealized3/left,idealized3/left]auth3 (i,j,l:index):
   [happens(FI(i,j,l))] ->
       [exec@FI(i,j,l)] ->
        Exists (k:index),
          [I(i,j,l) < FI(i,j,l) &&
          SR(j,k,i) < FI(i,j,l) &&
          input@SR(j,k,i) =  output@I(i,j,l) &&
          fst(output@SR(j,k,i)) = fst(input@FI(i,j,l)) &&
          fst(snd(output@SR(j,k,i))) = fst(snd(input@FI(i,j,l))) &&
          snd(snd(output@SR(j,k,i))) = snd(snd(input@FI(i,j,l)))].

equiv  [idealized3/left,idealized3/left] dummy.
Proof.
  diffeq => *.
Qed.

(*******************************************)
(*** Strong Secrecy of the responder key ***)
(*******************************************)

axiom  [idealized3/left,idealized3/left]  fst_p: forall (x,y:message) fst(<x,y>)=x.
axiom  [idealized3/left,idealized3/left]  snd_p: forall (x,y:message) snd(<x,y>)=y.

name n_PRF2 : index * index * index -> message.
 (* multi PRF assumption, F1(_,n) and F2(_,n) can be seen as F1(_,n') and F2(_,n) *)
axiom  [idealized3/left,idealized3/left] multprf (i,j,k:index,m:message): F1(m,n_PRF(i,j,k)) = F1(m,n_PRF2(i,j,k)).

axiom   [idealized3/left,idealized3/left] len_F (x1,x2:message) : len(F1(x1,x2)) = len(skex).

(* In idealized, we prove that at the end of I, the derived key is strongly secret. *)
global goal [idealized3/left,idealized3/left] resp_key (i,j,k:index[param]):
 [happens(FI(i,j,k))] -> 
 [exec@FI(i,j,k)] -> 
 equiv(frame@FI(i,j,k), diff(sIR i j k@FI(i,j,k), ikIR(i,j,k))) .
Proof.
  intro Hap Ex.
  use dummy with FI(i,j,k) => //.
  expand sIR.
  expand kj10.
  expand FK1.
  use auth3 with i,j,k => //.
  destruct H0 as [k0 H0'].
  have ->: (try find il,jl,kl such that
               fst(snd(input@FI(i,j,k))) =
               encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
             in F1(sid10(i,j,k)@FI(i,j,k),n_PRF(il,jl,kl))
             else F1(sid10(i,j,k)@FI(i,j,k),
                  exct(skex,decap(fst(snd(input@FI(i,j,k))),vkI(i)))))
             =
              F1(sid10(i,j,k)@FI(i,j,k),n_PRF(i,j,k0)).
    + localize H0' as H0. clear H0'. repeat destruct H0.
      expand output.
      rewrite ?snd_p in Meq0, Meq, Meq1.
      rewrite ?fst_p in  Meq0, Meq, Meq1.
      expand C4.
      case try find il,jl,kl such that _ in  F1(sid10(i,j,k)@FI(i,j,k),n_PRF(il,jl,kl)) else _.
        ++ intro [i1 j1 k1 [I1 I2]].
           rewrite I2.
           have U :
           decap(encap(n_CCA(i1,j1,k1),rk(i1,j1,k1),epk(vkI(i1))), vkI(i1)) =
           decap(encap(n_CCA(i,j,k0),rk(i,j,k0),epk(vkI(i))), vkI(i1)) by auto.
           rewrite !decap_encap in U. 
           by fresh U.

        ++ intro [I F]. 
           by use I with i,j,k0.

    + rewrite multprf.
      prf 1, F1(_,n_PRF2(i,j,k0)); rewrite if_true in 1 => //.
      xor 1; rewrite if_true in 1.
      rewrite len_F; 1: by namelength skex,n_PRF1.
      by fresh 1.
Qed.


(* In idealized, we prove that at the end of R, the derived key is strongly secret. *)
global goal [idealized3/left,idealized3/left] init_key (i,j,k:index[param]):
 [happens(SR(j,k,i))] -> 
 [exec@SR(j,k,i)] -> 
 equiv(frame@SR(j,k,i), diff(sRI i j k@SR(j,k,i), ikIR(j,k,i))).
Proof.
  intro Hap Ex.
  use dummy with SR(j,k,i) => //.
  expand sRI.
  expand kj8.

  rewrite multprf.
  prf 1, F1(_,n_PRF2(i,j,k)); rewrite if_true in 1 => //.
  xor 1; rewrite if_true in 1.
  rewrite len_F.
  namelength skex,n_PRF1.
  auto.
  by fresh 1.
Qed.
