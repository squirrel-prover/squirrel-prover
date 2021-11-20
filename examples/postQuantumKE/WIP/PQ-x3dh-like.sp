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

All sessions only talk to honest sessions.

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



axiom [idealized] uniqepk : forall (m1,m2:message), epk(m1) =epk(m2) => m1=m2.

axiom [idealized] sufcma : forall (m1,m2,sk:message), checksign(m1,spk(sk)) = m2 => m1 =sign(m2,sk).

axiom [idealized] xorconcel : forall (m1,m2,m3:message) m1=m2 => xor(m1,xor(m2,m3)) = m3.

axiom [idealized] rcheck : forall (m1,m2,sk:message), m1=m2 => checksign(sign(m1,sk),spk(sk)) = m2.

axiom [idealized] snd_pair (x,y : message) : snd (<x, y >) = y.


goal [idealized] auth :  forall (i,j,l:index) ,
   happens(FI(i,j,l)) =>
        exec@FI(i,j,l) <=>
      exec@pred(FI(i,j,l)) &&
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
split.
expand exec.
expand cond.
euf H0.
assert ( SR(j,k,i0) <= FI(i,j,l) || SR(j,k,i0) < FI(i,j,l)) <=>  SR(j,k,i0) < FI(i,j,l).
case H1.
use H2.

use uniqepk with vkI(i),vkI(i0).
exists k.
depends I(i,j,l), FI(i,j,l).


use sufcma with  (xor(ktilde5(i,j,l)@FI(i,j,l),snd(snd(input@FI(i,j,l))))),  sid5(i,j,l)@FI(i,j,l)  ,  skR(j) .

case try find il,jl,kl such that
      fst(snd(input@FI(i,j,l))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in exct(skex,k(il,jl,kl))
    else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i))).



assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
decap( encap(n_CCA(i,j,k),rk(i,j,k),epk(vkI(i))), vkI(il)).
case H4.
case H5.
case H4.
case H6.

rewrite Meq2 in D3.

use H4 with i,j,k.


executable pred(FI(i,j,l)).
use H2 with DSR(j,k).
assert happens(DSR(j,k)).
case H1.
expand  exec@DSR(j,k).
expand cond.
use H4 with i.

case H1.

expand exec. expand cond.
depends I(i,j,l), FI(i,j,l).

case try find il,jl,kl such that
      fst(snd(input@FI(i,j,l))) =
      encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il)))
    in exct(skex,k(il,jl,kl))
    else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i))).



assert decap(   encap(n_CCA(il,jl,kl),rk(il,jl,kl),epk(vkI(il))), vkI(il)) =
decap( encap(n_CCA(i,j,k),rk(i,j,k),epk(vkI(i))), vkI(il)).
case H0.
case H1.
case H0.
case H2.
rewrite Meq4 in D12.

rewrite -Meq.
expand output.
rewrite snd_pair.
rewrite snd_pair.

assert ktilde5(i,j,l)@FI(i,j,l) = ktilde3(j,k,i)@SR(j,k,i).
rewrite Meq5.

use xorconcel with ktilde3(j,k,i)@SR(j,k,i), ktilde3(j,k,i)@SR(j,k,i), sign(sid3(j,k,i)@SR(j,k,i),skR(j)).
rewrite Meq6.

use rcheck with sid3(j,k,i)@SR(j,k,i), sid5(i,j,l)@FI(i,j,l), skR(j).

use H0 with i,j,l.

Qed.

(* As I1 is the converse of FI, we also have freely that *)
axiom [idealized] auth2 :  forall (i,j,l:index) ,
   happens(I1(i,j,l)) =>
        exec@I1(i,j,l) <=>
      exec@pred(I1(i,j,l)) &&
        not(exists (l2:index),
          I(i,j,l) < I1(i,j,l) &&
          SR(j,k,i) < I1(i,j,l) &&
          input@SR(j,k,i) =  output@I(i,j,l) &&
          fst(output@SR(j,k,i)) = fst(input@I1(i,j,l)) &&
          fst(snd(output@SR(j,k,i))) = fst(snd(input@I1(i,j,l))) &&
          snd(snd(output@SR(j,k,i))) = snd(snd(input@I1(i,j,l))))
.


equiv [idealized] step1.
Proof.
enrich skex. enrich seq(i->epk(vkI(i))).
enrich seq(i,j,l -> kt(j,i,l)).
enrich seq(i,j,l -> rkt(j,i,l)).
enrich seq(j-> vkR(j)).
enrich seq(i,j,l->k(j,i,l)).
enrich seq(j-> skR(j)).
enrich seq(i,j,l-> epk(dkt(i,j,l))).
induction t.

expandall.


expandall. fa 8.

expandall. fa 8. repeat fa 9.
expandseq seq(i->epk(vkI(i))), i.
fa 12. repeat fa 13. repeat fa 15.

cca1 12.
equivalent len(diff(k(j,i,l),rnd(j,i,l))), len(skex).
project.
help.
namelength k(j,i,l), skex.
namelength rnd(j,i,l), skex.
expandseq seq(i,j,l->k(j,i,l)),i,j,l.
expandseq seq(i,j,l->kt(j,i,l)),i,j,l.
expandseq seq(i,j,l->rkt(j,i,l)),i,j,l.
expandseq seq(j->vkR(j)),j.
expandseq seq(j->skR(j)),j.


expandall.
fa 8. fa 9. fa 9.
expandseq seq(i,j,l-> epk(dkt(i,j,l))),i,j,l.


expand frame.
equivalent         exec@FI(i,j,l),
      exec@pred(FI(i,j,l)) &&
        exists (l2:index),
          I(i,j,l) < FI(i,j,l) &&
          SR(j,k,i) < FI(i,j,l) &&
          input@SR(j,k,i) =  output@I(i,j,l) &&
          fst(output@SR(j,k,i)) = fst(input@FI(i,j,l)) &&
          fst(snd(output@SR(j,k,i))) = fst(snd(input@FI(i,j,l))) &&
          snd(snd(output@SR(j,k,i))) = snd(snd(input@FI(i,j,l))).

nosimpl(use auth with i,j,l).
assumption.
assumption.
fa 8.
fa 9.
fa 10.
expand output.
fadup 9.

expand frame.
equivalent        exec@I1(i,j,l),
      exec@pred(I1(i,j,l)) &&
        not(exists (l2:index),
          I(i,j,l) < I1(i,j,l) &&
          SR(j,k,i) < I1(i,j,l) &&
          input@SR(j,k,i) =  output@I(i,j,l) &&
          fst(output@SR(j,k,i)) = fst(input@I1(i,j,l)) &&
          fst(snd(output@SR(j,k,i))) = fst(snd(input@I1(i,j,l))) &&
          snd(snd(output@SR(j,k,i))) = snd(snd(input@I1(i,j,l)))).
nosimpl(use auth2 with i,j,l); assumption.

fa 8. fa 9.
 fa 10. fadup 9.
Qed.

(*******************************************)
(************ One more step with PRF *******)

(* On the left, right projection of the ideal system, and with some macro removal. *)
(* On the right, idealized exct *)
name rndp : index -> index -> index -> message.

process InitiatorIdeal2(i,j,l:index) =
(* Initiator i who wants to talk to Responder j *)

 out(cI, epk(dkt(i,j,l)) );

 in(cR,m);

 let KT = decap( fst(m),dkt(i,j,l) ) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <  epk(dkt(i,j,l)), <fst(snd(m)), fst(m)>>>> in
   let K1 =
    try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
     exct(skex,k(j2,i2,l2))
    else
      exct(skex,decap( fst(snd(m)), vkI(i)))
   in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,
    try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
     diff(exct(skex,k(j2,i2,l2)) , rndp(l2,j2,i2))
    else
      exct(skex,decap( fst(snd(m)), vkI(i)))
) XOR F1(sid,K2) in

   if checksign( F2(sid,
    try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
     diff(exct(skex,k(j2,i2,l2)) , rndp(l2,j2,i2))
    else
      exct(skex,decap( fst(snd(m)), vkI(i)))
) XOR F2(sid,K2)  XOR snd(snd(m)), spk(skR(j))) = sid then
      FI : out(cR,ok).

process ResponderIdeal2(j,i,l:index) =
(* Responder j who is willing to talk to initator i *)
    in(cR, m);

   let CT = encap(kt(j,i,l), rkt(j,i,l), m) in
   let C = encap(rnd(j,i,l), rk(j,i,l), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K2 = exct(skex,kt(j,i,l)) in
   let kj = F1(sid,      diff(exct(skex,k(j,i,l)) , rndp(l,j,i)) ) XOR F1(sid,K2) in
   SR : out(cR,<CT,<C,  F2(sid,  diff(exct(skex,k(j,i,l)) , rndp(l,j,i)) ) XOR F2(sid,K2) XOR sign(sid, skR(j))   >>).

system [Ideal2]  out(cI,skex); ((!_j !_i !_l R: ResponderIdeal2(j,i,l)) | (!_i !_j !_l I: InitiatorIdeal2(i,j,l))).

axiom [Ideal2] fstpair : forall (m1,m2:message), fst(<m1,m2>) = m1.

axiom [Ideal2] decenc : forall (m1,m2,m3   :message),   decap(encap(m1,m2,epk(m3)),m3) = m1.

equiv [Ideal2] trans.
Proof.
globalprf seq(kj,ki,kl -> exct(skex,k(kj,ki,kl))) , news.
print.
rename seq(i,j,l -> n_PRF(i,j,l)), seq(i,j,l -> rndp(i,j,l)), newsss.
print.
diffeq.

case (try find kl,kj,ki such that (skex = skex && (kj = j && ki = i && kl = l))
 in rndp(kl,kj,ki) else exct(skex,k(j,i,l))).
substeq Meq0.
case (try find kl,kj,ki such that (skex = skex && (kj = j && ki = i && kl = l))
 in rndp(kl,kj,ki) else exct(skex,k(j,i,l))).

by use H1 with kl,kj,ki.
by use H1 with l,j,i.

case    try find i2,j2,l2 such that
                    KT2(i,j,l)@FI(i,j,l) = kt(j2,i2,l2)
                  in
                    try find kl,kj,ki such that
                      (skex = skex && (kj = j2 && ki = i2 && kl = l2))
                    in rndp(kl,kj,ki) else exct(skex,k(j2,i2,l2))
                  else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i))).
substeq Meq0. substeq Meq0.

case   try find kl,kj,ki such that
                    (skex = skex && (kj = j2 && ki = i2 && kl = l2))
                  in rndp(kl,kj,ki) else exct(skex,k(j2,i2,l2)).
substeq Meq1.

case  try find i3,j3,l3 such that
                    KT2(i,j,l)@FI(i,j,l) = kt(j3,i3,l3)
                  in rndp(l3,j3,i3)
                  else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i))).
substeq Meq1.
by use H1 with ki,kj,kl.
by use H1 with l2,j2,i2.


forceuse auth with i,j,l. use H2.
use H1 with i,j,l2.
expand output.

substeq fst(input@FI(i,j,l)), CT2(j,k,i)@SR(j,k,i).
forceuse fstpair with CT2(j,k,i)@SR(j,k,i),
         diff(
           <C2(j,k,i)@SR(j,k,i),
            xor(xor(F2(sid4(j,k,i)@SR(j,k,i),
                    try find kl,kj,ki such that
                      (skex = skex && (kj = j && ki = i && kl = l2))
                    in rndp(kl,kj,ki) else exct(skex,k(j,k,i))),
                F2(sid4(j,k,i)@SR(j,k,i),K10(j,k,i)@SR(j,k,i))),
            sign(sid4(j,k,i)@SR(j,k,i),skR(j)))>,
           <C2(j,k,i)@SR(j,k,i),
            xor(xor(F2(sid4(j,k,i)@SR(j,k,i),rndp(l2,j,i)),
                F2(sid4(j,k,i)@SR(j,k,i),K10(j,k,i)@SR(j,k,i))),
            sign(sid4(j,k,i)@SR(j,k,i),skR(j)))>).
substeq Meq2.
case (try find kl,kj,ki such that (skex = skex && (kj = j && ki = i && kl = l))
 in rndp(kl,kj,ki) else exct(skex,k(j,i,l))).
by use H1 with l,j,i.
Qed.





(*******************************************)
(************ Final before ROR proofs *******)

name rndp2 : index -> index -> index -> message.
(* Multi PRF assumption, we can replace rndp by rndp2 in F2. *)

name ideal : index -> index -> index -> index -> message.
process InitiatorIdeal3(i,j,l:index) =
(* Initiator i who wants to talk to Responder j *)

 out(cI, epk(dkt(i,j,l)) );

 in(cR,m);

 let KT = decap( fst(m),dkt(i,j,l) ) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <  epk(dkt(i,j,l)), <fst(snd(m)), fst(m)>>>> in

   let K2 = exct(skex,KT) in

   if checksign( F2(sid,
    try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
 rndp2(l2,j2,i2)
    else
      exct(skex,decap( fst(snd(m)), vkI(i)))
) XOR F2(sid,K2)  XOR snd(snd(m)), spk(skR(j))) = sid then
      FI : out(cR, diff( try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
	  F1(sid, rndp(l2,j2,i2))
    else
      F1(sid, exct(skex,decap( fst(snd(m)), vkI(i)))),
try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
	  ideal(l,l2,j2,i2)
    else
fail)
 XOR F1(sid,K2)).

process ResponderIdeal3(j,i,l:index) =
(* Responder j who is willing to talk to initator i *)
    in(cR, m);

   let CT = encap(kt(j,i,l), rkt(j,i,l), m) in
   let C = encap(rnd(j,i,l), rk(j,i,l), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K2 = exct(skex,kt(j,i,l)) in
   SR : out(cR,<CT,<C,  F2(sid,  rndp2(l,j,i) ) XOR F2(sid,K2) XOR sign(sid, skR(j))   >>);

   FR : out(cR,
diff( F1(sid,     rndp(l,j,i) ),
try find l2 such that m= epk(dkt(i,j,l2)) in
ideal(l2,l,j,i)
else   F1(sid,     rndp(l,j,i) )

)
XOR F1(sid,K2)).
system [Ideal3]  out(cI,skex); ((!_j !_i !_l R: ResponderIdeal3(j,i,l)) | (!_i !_j !_l I: InitiatorIdeal3(i,j,l))).

equiv [Ideal3]  t.
Proof.

globalprf seq(mi,mj,ml,ml2 ->
   F1(     < epk(vkI(mi)), <epk(vkR(mj)), <epk(dkt(mi,mj,ml2)) , <encap(rnd(mj,mi,ml), rk(mj,mi,ml), epk(vkI(mi))) , encap(kt(mj,mi,ml), rkt(mj,mi,ml), epk(dkt(mi,mj,ml2))) >>>>
 , rndp(ml,mj,mi))
 ), newws.
rename seq(i,j,l,k -> n_PRF(i,j,l,k)), seq(i,j,l,k -> ideal(i,j,l,k)), newsss.
print.
diffeq.

nosimpl(forceuse auth with i,j,l).
use H2. use H2.
notleft H0.
by use H0 with i,j,l2.

nosimpl(forceuse auth with i,j,l).
use H2. simpl.

case (try find ml2,ml3,mj,mi such that
   (sid7(i,j,l)@FI(i,j,l) =
    <epk(vkI(mi)),
     <epk(vkR(mj)),
      <epk(dkt(mi,mj,ml2)),
       <encap(rnd(mj,mi,ml3),rk(mj,mi,ml3),epk(vkI(mi))),
        encap(kt(mj,mi,ml3),rkt(mj,mi,ml3),epk(dkt(mi,mj,ml2)))>>>> &&
    (ml3 = l0 && mj = j0 && mi = i0))
 in ideal(ml2,ml3,mj,mi) else F1(sid7(i,j,l)@FI(i,j,l),rndp(l0,j0,i0))).
substeq Meq0. substeq Meq0.
nosimpl(forceuse auth with i,j,l).
use H1.  use H1.
by forceuse uniqepk with dkt(i,j,l), dkt(i,j,ml2).

auto.

nosimpl(forceuse auth with i,j,l).
use H2. use H2.


by use H1 with l,l0,j,i.
auto.


case  (try find ml2,ml3,mj,mi such that
   (sid6(j,i,l)@FR(j,i,l) =
    <epk(vkI(mi)),
     <epk(vkR(mj)),
      <epk(dkt(mi,mj,ml2)),
       <encap(rnd(mj,mi,ml3),rk(mj,mi,ml3),epk(vkI(mi))),
        encap(kt(mj,mi,ml3),rkt(mj,mi,ml3),epk(dkt(mi,mj,ml2)))>>>> &&
    (ml3 = l && mj = j && mi = i))
 in ideal(ml2,ml3,mj,mi) else F1(sid6(j,i,l)@FR(j,i,l),rndp(l,j,i))) .
substeq Meq. substeq Meq.

case try find l2 such that input@SR(mj,mi,l) = epk(dkt(mi,mj,l2))
in ideal(l2,l,mj,mi) else F1(sid6(mj,mi,l)@FR(mj,mi,l),rndp(l,mj,mi)).
substeq Meq1. substeq Meq1.
by forceuse uniqepk with dkt(mi,mj,ml2), dkt(mi,mj,l2).

by use H2 with ml2.

case try find l2 such that input@SR(j,i,l) = epk(dkt(i,j,l2))
in ideal(l2,l,j,i) else F1(sid6(j,i,l)@FR(j,i,l),rndp(l,j,i)).

by use H2 with l2,l,j,i.
Qed.


(*******************************************)
(************  Final games           *******)


(* Multi PRF assumption, we can replace rndp by rndp2 in F2. *)


process InitiatorIdeal4(i,j,l:index) =
(* Initiator i who wants to talk to Responder j *)

 out(cI, epk(dkt(i,j,l)) );

 in(cR,m);

 let KT = decap( fst(m),dkt(i,j,l) ) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <  epk(dkt(i,j,l)), <fst(snd(m)), fst(m)>>>> in

   let K2 = exct(skex,KT) in

   if checksign( F2(sid,
    try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
 rndp2(l2,j2,i2)
    else
      exct(skex,decap( fst(snd(m)), vkI(i)))
) XOR F2(sid,K2)  XOR snd(snd(m)), spk(skR(j))) = sid then
      FI : out(cR,
(try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
	  ideal(l,l2,j2,i2)
    else
fail)
 XOR F1(sid,K2)).

process ResponderIdeal4(j,i,l:index) =
(* Responder j who is willing to talk to initator i *)
    in(cR, m);

   let CT = encap(kt(j,i,l), rkt(j,i,l), m) in
   let C = encap(rnd(j,i,l), rk(j,i,l), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K2 = exct(skex,kt(j,i,l)) in
   SR : out(cR,<CT,<C,  F2(sid,  rndp2(l,j,i) ) XOR F2(sid,K2) XOR sign(sid, skR(j))   >>);

   FR : out(cR,

(try find l2 such that m= epk(dkt(i,j,l2)) in
ideal(l2,l,j,i)
else   F1(sid,     rndp(l,j,i) )

)
XOR F1(sid,K2)).

system [Final]  out(cI,skex); ((!_j !_i !_l R: ResponderIdeal4(j,i,l)) | (!_i !_j !_l I: InitiatorIdeal4(i,j,l))).
