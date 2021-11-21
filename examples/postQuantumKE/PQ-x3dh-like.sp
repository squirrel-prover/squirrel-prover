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

hash exct

(* public random key for exct *)

name skex : message

(* KEM *)

aenc encap,decap,epk

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
name dkt : index-> index -> index -> message


(* session randomess of R *)
name kt : index  -> index  -> index ->message
name k : index  -> index  -> index -> message
name rkt : index  -> index  -> index ->message
name rk : index  -> index  -> index -> message

(* session randomess of R with dishonnest I *)
name Dkt :  index  -> index ->message
name Dk :  index  -> index -> message
name Drkt :  index  -> index ->message
name Drk :  index  -> index -> message

(* key derivation storage *)
mutable sIR(i,j,k:index) : message =  zero
mutable sRI(i,j,k:index) : message =  zero
mutable DsRI(j,k:index) : message =  zero

(* ideal keys *)
name ikIR : index -> index -> index -> message


abstract ok:message

channel cI
channel cR.

(* Main protocol Model *)
(***********************)

(* Initiator vkI(i) who wants to talk to Responder spk(skR(j)) *)
process Initiator(i,j,k:index) =
   out(cI, epk(dkt(i,j,k)) );

   in(cR,m);

   let KT = decap( fst(m),dkt(i,j,k) ) in

   let sid = < epk(vkI(i)), <epk(vkR(j)), <epk(dkt(i,j,k)) , <fst(snd(m)), fst(m)>>>> in
   let K1 = exct(skex,decap( fst(snd(m)), vkI(i) )) in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   if checksign( ktilde XOR snd(snd(m)), spk(skR(j))) = sid then
    FI :  sIR(i,j,k) := kj.

process Responder(j,k:index) =
(* Responder j who is willing to talk to initator i *)
   in(cR, epkI);
    in(cR, m);
  try find i such that epkI = epk(vkI(i)) in
   let CT = encap(kt(i,j,k), rkt(i,j,k), m) in
   let C = encap(k(i,j,k), rk(i,j,k), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,k(i,j,k)) in
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

system [main]  out(cI,skex); ((!_j !_k R: Responder(j,k)) | (!_i !_j !_k I: Initiator(i,j,k))).


system mainCCAkR = [main/left] with gcca (il,jl,kl:index),  encap(k(il,jl,kl), rk(il,jl,kl), epk(vkI(il))).

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
       exct(skex,k(il,jl,kl))
     else
       exct(skex,decap( fst(snd(m)), vkI(i) ))
   in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   if checksign( ktilde XOR snd(snd(m)), spk(skR(j))) = sid then
     FI:  sIR(i,j,k) := kj.

process Responder2(j,k:index) =
(* Responder j who is willing to talk to initator i *)
   in(cR, epkI);
    in(cR, m);
  try find i such that epkI = epk(vkI(i)) in
   let CT = encap(kt(i,j,k), rkt(i,j,k), m) in
   let C = encap(n_CCA(i,j,k), rk(i,j,k), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,k(i,j,k)) in
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

system [idealized]  out(cI,skex); ((!_j !_k R: Responder2(j,k)) | (!_i !_j !_k I: Initiator2(i,j,k))).

axiom [mainCCAkR/left,idealized/left] tf: forall (x,y,z:message), decap(encap(x,y,epk(z)),z)=x.

(* We prove that the original game, after transitivity to mainCCAkI, is equivalent to idealized. *)
equiv [mainCCAkR/left,idealized/left] test.
Proof.

diffeq.

case try find il,jl,kl such that _ in k(il,jl,kl) else _.
rewrite Meq0.

case try find il,jl,kl such that _ in exct(skex, k(il,jl,kl)) else _.
rewrite Meq2.

assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).

case H1.
case H2.

use H1 with il,jl,kl.


case try find il,jl,kl such that _ in  exct(skex,k(il,jl,kl)) else _.
use H1 with il,jl,kl.

case try find il,jl,kl such that _ in  k(il,jl,kl) else _.
rewrite Meq0.
case try find il,jl,kl such that _ in exct(skex, k(il,jl,kl)) else _.
rewrite Meq2.



assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).

case H1.
case H2.

use H1 with il,jl,kl.

case try find il,jl,kl such that _ in exct(skex,k(il,jl,kl)) else _.
use H1 with il,jl,kl.

case try find il,jl,kl such that _ in  k(il,jl,kl) else _.
rewrite Meq0.
case try find il,jl,kl such that _ in exct(skex, k(il,jl,kl)) else _.
rewrite Meq2.


assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))  , vkI(il)) = decap(   encap(n_CCA(il0,jl0,kl0),rk(il0,jl0,kl0),epk(vkI(il0))) , vkI(il)).
case H1.
case H2.

use H1 with il,jl,kl.

case try find il,jl,kl such that _ in exct(skex,k(il,jl,kl)) else _.
use H1 with il,jl,kl.
Qed.


system idealized2 = [idealized/left] with gprf (iv,jv,kv:index),  exct(skex,k(iv,jv,kv)).

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
   if checksign( ktilde XOR snd(snd(m)), spk(skR(j))) = sid then
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

system [idealized3]  out(cI,skex); ((!_j !_k R: Responder3(j,k)) | (!_i !_j !_k I: Initiator3(i,j,k))).

axiom [idealized3/left,idealized2/left] ifte (i,j,k:index): att(frame@pred(FI(i,j,k))) =  att(frame@pred(I1(i,j,k))).

goal  [idealized3/left,idealized2/left] trans_eq (i,j,k:index):
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
      exct(skex,decap(fst(snd(att(frame@pred(I1(i,j,k))))),vkI(i)))),
F2(<epk(vkI(i)),
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
      in n_PRF(iv,jv,kv) else exct(skex,k(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(I1(i,j,k))))),vkI(i)))),
F2(<epk(vkI(i)),
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
rewrite Meq0.

case   try find il,jl,kl such that
      fst(snd(att(frame@pred(I1(i,j,k))))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in
 _
    else exct(skex,decap(fst(snd(att(frame@pred(I1(i,j,k))))),vkI(i))).
rewrite Meq2.

case   try find iv,jv,kv such that
      (skex = skex && (il0 = iv && jl0 = jv && kl0 = kv))
    in n_PRF(iv,jv,kv) else exct(skex,k(il0,jl0,kl0)).
rewrite Meq3.

assert decap( encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
decap(   encap(n_CCA(iv,jv,kv),rk(iv,jv,kv),epk(vkI(iv))), vkI(il)).
case H.
case H0.

use H with il0,jl0,kl0.
use H with il,jl,kl.

case   try find il,jl,kl such that
      fst(snd(att(frame@pred(I1(i,j,k))))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in
      try find iv,jv,kv such that
        (skex = skex && (il = iv && jl = jv && kl = kv))
      in n_PRF(iv,jv,kv) else exct(skex,k(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(I1(i,j,k))))),vkI(i))).


rewrite Meq1.
use H with il,jl,kl.
Qed.

axiom [idealized3/left,idealized2/left]  fasign : forall (m1,m2,m3:message), m1=m2 => checksign(m1,m3) = checksign(m2,m3).


goal  [idealized3/left,idealized2/left] trans_eq2 (i,j,k:index):
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
      exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i)))),
F1(<epk(vkI(i)),
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
      in n_PRF(iv,jv,kv) else exct(skex,k(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i)))),
F1(<epk(vkI(i)),
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
rewrite Meq0.

case  try find il,jl,kl such that
      fst(snd(att(frame@pred(FI(i,j,k))))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in
      try find iv,jv,kv such that
        (skex = skex && (il = iv && jl = jv && kl = kv))
      in n_PRF(iv,jv,kv) else exct(skex,k(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i))).
rewrite Meq2.

case  try find iv,jv,kv such that
      (skex = skex && (il0 = iv && jl0 = jv && kl0 = kv))
    in n_PRF(iv,jv,kv) else exct(skex,k(il0,jl0,kl0)).
rewrite Meq3.
assert decap( encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
decap(   encap(n_CCA(iv,jv,kv),rk(iv,jv,kv),epk(vkI(iv))), vkI(il)).
case H.
case H0.
use H with il0,jl0,kl0.

use H with il,jl,kl.

case     try find il,jl,kl such that
      fst(snd(att(frame@pred(FI(i,j,k))))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in
      try find iv,jv,kv such that
        (skex = skex && (il = iv && jl = jv && kl = kv))
      in n_PRF(iv,jv,kv) else exct(skex,k(il,jl,kl))
    else exct(skex,decap(fst(snd(att(frame@pred(FI(i,j,k))))),vkI(i))).
use H with il,jl,kl.
Qed.


equiv [idealized3/left,idealized2/left] transitivity.
Proof.
diffeq.
use trans_eq with i,j,k.

use trans_eq2 with i,j,k.

use ifte with i,j,k.
use trans_eq with i,j,k.
rewrite -Meq in Meq0.
rewrite -Meq0.

admit. (* TODO: this is a bug witness in the congruence closure. *)

case  try find iv,jv,kv such that (skex = skex && (i = iv && j = jv && k = kv))
    in n_PRF(iv,jv,kv) else exct(skex,k(i,j,k)).
rewrite Meq.
use H1 with i,j,k.

case    try find iv,jv,kv such that (skex = skex && (i = iv && j = jv && k = kv))
    in n_PRF(iv,jv,kv) else exct(skex,k(i,j,k)).
rewrite Meq.
use H1 with  i,j,k.
Qed.

axiom [idealized3] uniqepk : forall (m1,m2:message), epk(m1) =epk(m2) => m1=m2.

axiom [idealized3] sufcma : forall (m1,m2,sk:message), checksign(m1,spk(sk)) = m2 => m1 =sign(m2,sk).

axiom [idealized3] xorconcel : forall (m1,m2,m3:message) m1=m2 => xor(m1,xor(m2,m3)) = m3.

axiom [idealized3] rcheck : forall (m1,m2,sk:message), m1=m2 => checksign(sign(m1,sk),spk(sk)) = m2.

axiom [idealized3] snd_pair (x,y : message) : snd (<x, y >) = y.


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
expand exec.
expand cond.
euf H0.
assert ( SR(j,k,i0) <= FI(i,j,l) || SR(j,k,i0) < FI(i,j,l)) <=>  SR(j,k,i0) < FI(i,j,l).
case H1.
use H2.

use uniqepk with vkI(i),vkI(i0).
exists k.
depends I(i,j,l), FI(i,j,l).


use sufcma with  (xor(ktilde8(i,j,l)@FI(i,j,l),snd(snd(input@FI(i,j,l))))),  sid8(i,j,l)@FI(i,j,l)  ,  skR(j) .
expand output.
rewrite snd_pair.
rewrite snd_pair.

use xorconcel with ktilde6(j,k,i)@SR(j,k,i), ktilde6(j,k,i)@SR(j,k,i), sign(sid6(j,k,i)@SR(j,k,i),skR(j)).
rewrite -Meq in Meq0.
rewrite -Meq0.

assert ktilde6(j,k,i)@SR(j,k,i)=ktilde8(i,j,l)@FI(i,j,l).

case  try find il,jl,kl such that
      fst(snd(input@FI(i,j,l))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in F2(sid8(i,j,l)@FI(i,j,l),n_PRF(il,jl,kl))
    else
      F2(sid8(i,j,l)@FI(i,j,l),
      exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i)))).
rewrite Meq3 in D3.

expand ktilde6,ktilde8.
assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
decap( encap(n_CCA(i,j,k),rk(i,j,k),epk(vkI(i))), vkI(il)).

case H4.
case H5.

use H4 with i,j,k.


executable pred(FI(i,j,l)).
use H2 with DSR(j,k).
assert happens(DSR(j,k)).
case H1.
expand  exec@DSR(j,k).
expand cond.
use H4 with i.

case H1.
Qed.
(* As I1 is the converse of FI, we also have freely that *)


global axiom  [idealized3/left,idealized3/left]auth3 :  forall (i,j,l:index) ,
   [happens(FI(i,j,l))] ->
       [exec@FI(i,j,l)] ->
        exists (k:index),
          [I(i,j,l) < FI(i,j,l) &&
          SR(j,k,i) < FI(i,j,l) &&
          input@SR(j,k,i) =  output@I(i,j,l) &&
          fst(output@SR(j,k,i)) = fst(input@FI(i,j,l)) &&
          fst(snd(output@SR(j,k,i))) = fst(snd(input@FI(i,j,l))) &&
          snd(snd(output@SR(j,k,i))) = snd(snd(input@FI(i,j,l)))]
.


equiv  [idealized3/left,idealized3/left] dummy.
Proof.
diffeq.
Qed.

(*******************************************)
(*** Strong Secrecy of the responder key ***)
(*******************************************)
set autoIntro = false.
axiom  [idealized3/left,idealized3/left]  fst_p: forall (x,y:message) fst(<x,y>)=x.
axiom  [idealized3/left,idealized3/left]  snd_p: forall (x,y:message) snd(<x,y>)=y.

name n_PRF2 : index -> index -> index -> message.
 (* multi PRF assumption, F1(_,n) and F2(_,n) can be seen as F1(_,n') and F2(_,n) *)
axiom  [idealized3/left,idealized3/left] multprf (i,j,k:index,m:message): F1(m,n_PRF(i,j,k)) = F1(m,n_PRF2(i,j,k)).

axiom   [idealized3/left,idealized3/left] len_F (x1,x2:message) : len(F1(x1,x2)) = len(skex).

(* In idealized, we prove that at the end of I, the derived key is strongly secret. *)
global goal [idealized3/left,idealized3/left] resp_key: forall (i,j,k:index), [happens(FI(i,j,k))] -> [exec@FI(i,j,k)] -> equiv(frame@FI(i,j,k), diff(sIR(i,j,k)@FI(i,j,k), ikIR(i,j,k))) .
Proof.

intro i j k Hap Ex.
use dummy with FI(i,j,k).
expand sIR.
expand kj8.
expand FK1.


use auth3 with i,j,k.




destruct H0.

equivalent try find il,jl,kl such that
           fst(snd(input@FI(i,j,k))) =
           encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
         in F1(sid8(i,j,k)@FI(i,j,k),n_PRF(il,jl,kl))
         else
           F1(sid8(i,j,k)@FI(i,j,k),
           exct(skex,decap(fst(snd(input@FI(i,j,k))),vkI(i)))),
          F1(sid8(i,j,k)@FI(i,j,k),n_PRF(i,j,k0)).

repeat destruct H0.
expand output.
rewrite ?snd_p in Meq0, Meq, Meq1.
rewrite ?fst_p in  Meq0, Meq, Meq1.
expand C4.

case try find il,jl,kl such that _ in  F1(sid8(i,j,k)@FI(i,j,k),n_PRF(il,jl,kl)) else _.

intro [i1 j1 k1 [I1 I2]].
rewrite I2.
assert decap(   encap(n_CCA(i1,j1,k1),rk(i1,j1,k1),epk(vkI(i1))), vkI(i1)) =
decap(encap(n_CCA(i,j,k0),rk(i,j,k0),epk(vkI(i))), vkI(i1)) .

auto.

simpl.
case H1 => //.

intro [I F].
use I with i,j,k0.
auto.

rewrite multprf.
prf 1, F1(_,n_PRF2(i,j,k0)); yesif 1 => //.
xor 1; yesif 1.
rewrite len_F.
namelength skex,n_PRF1.auto.
fresh 1.
auto.

auto.
auto.
auto.
Qed.


(* In idealized, we prove that at the end of R, the derived key is strongly secret. *)
global goal [idealized3/left,idealized3/left] init_key: forall (i,j,k:index), [happens(SR(j,k,i))] -> [exec@SR(j,k,i)] -> equiv(frame@SR(j,k,i), diff(sRI(i,j,k)@SR(j,k,i), ikIR(j,k,i))) .
Proof.

intro i j k Hap Ex.
use dummy with SR(j,k,i) => //.
expand sRI.
expand kj6.

rewrite multprf.
prf 1, F1(_,n_PRF2(i,j,k)); yesif 1 => //.
xor 1; yesif 1.
rewrite len_F.
namelength skex,n_PRF1.auto.
fresh 1.

auto.
Qed.
