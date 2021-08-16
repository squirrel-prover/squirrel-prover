(*******************************************************************************

PQ X3DH


[A] Keitaro Hashimoto,Shuichi Katsumata, Kris Kwiatkowski, Thomas Prest. An Efficient and Generic Construction for Signal’s Handshake (X3DH): Post-Quantum, State Leakage Secure, and Deniable.

# Description

This protocol is a PQ sound version of X3DH. We model the basic handshake.

# Protocol parameters

Each party has two pairs of keys, one for kem and one for signatures

eki = epk(vki)
dki = spk(ski)


I(i)                        R(j)
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

(* ideal keys *)


abstract ok:message.

channel cI.
channel cR.

(* Main protocol Model *)

process Initiator(i,j,l:index) =
(* Initiator i who wants to talk to Responder j *)

 out(cI, epk(dkt(i,j,l)) );

 in(cR,m);

 let KT = decap( fst(m),dkt(i,j,l) ) in
  let K = decap( fst(snd(m)), vkI(i) ) in

   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <fst(snd(m)), fst(m)>>>> in
   let K1 = exct(skex,K) in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   if checksign( ktilde XOR snd(snd(m)), spk(skR(j))) = sid then
      FI : out(cR,ok).

process Responder(j,i,l:index) =
(* Responder j who is willing to talk to initator i *)
    in(cR, m);

   let CT = encap(kt(j,i,l), rkt(j,i,l), m) in
   let C = encap(k(j,i,l), rk(j,i,l), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,k(j,i,l)) in
   let K2 = exct(skex,kt(j,i,l)) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   SR : out(cR,<CT,<C, ktilde XOR sign(sid, skR(j))   >>).

system [Main]  out(cI,skex); ((!_j !_i !_l R: Responder(j,i,l)) | (!_i !_j !_l I: Initiator(i,j,l))).


(***************************************)
(************ Hidding the share ********)



process InitiatorIdeal(i,j,l:index) =
(* Initiator i who wants to talk to Responder j *)

 out(cI, epk(dkt(i,j,l)) );

 in(cR,m);

 let KT = decap( fst(m),dkt(i,j,l) ) in
  let K = diff(decap( fst(snd(m)), vkI(i)),
try find i2,j2,l2 such that KT= kt(j2,i2,l2)  in
   k(j2,i2,l2)
else
decap( fst(snd(m)), vkI(i)))

 in

   let sid = < epk(vkI(i)), <epk(vkR(j)), <  epk(dkt(i,j,l)), <fst(snd(m)), fst(m)>>>> in
   let K1 = exct(skex,K) in
   let K2 = exct(skex,KT) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   if checksign( ktilde XOR snd(snd(m)), spk(skR(j))) = sid then
      FI : out(cR,ok).

name rnd : index -> index -> index -> message.

process ResponderIdeal(j,i,l:index) =
(* Responder j who is willing to talk to initator i *)
    in(cR, m);

   let CT = encap(kt(j,i,l), rkt(j,i,l), m) in
   let C = encap(diff(k(j,i,l),rnd(j,i,l)), rk(j,i,l), epk(vkI(i))) in
   let sid = < epk(vkI(i)), <epk(vkR(j)), <m , <C, CT>>>> in
   let K1 = exct(skex,k(j,i,l)) in
   let K2 = exct(skex,kt(j,i,l)) in
   let kj = F1(sid,K1) XOR F1(sid,K2) in
   let ktilde = F2(sid,K1) XOR F2(sid,K2) in
   SR : out(cR,<CT,<C, ktilde XOR sign(sid, skR(j))   >>).

system [Ideal]  out(cI,skex); ((!_j !_i !_l R: ResponderIdeal(j,i,l)) | (!_i !_j !_l I: InitiatorIdeal(i,j,l))).

axiom [Ideal] uniqepk : forall (m1,m2:message), epk(m1) =epk(m2) => m1=m2.

axiom [Ideal] sufcma : forall (m1,m2,sk:message), checksign(m1,spk(sk)) = m2 => m1 =sign(m2,sk).

axiom [Ideal] xorconcel : forall (m1,m2,m3:message) m1=m2 => xor(m1,xor(m2,m3)) = m3.

axiom [Ideal] rcheck : forall (m1,m2,sk:message), m1=m2 => checksign(sign(m1,sk),spk(sk)) = m2.

goal [Ideal] auth :  forall (i,j,l:index) ,
   happens(FI(i,j,l)) =>
        exec@FI(i,j,l) <=>
      exec@pred(FI(i,j,l)) &&
        exists (l2:index),
          I(i,j,l) < FI(i,j,l) &&
          SR(j,i,l2) < FI(i,j,l) &&
          input@SR(j,i,l2) =  output@I(i,j,l) &&
          fst(output@SR(j,i,l2)) = fst(input@FI(i,j,l)) &&
          fst(snd(output@SR(j,i,l2))) = fst(snd(input@FI(i,j,l))) &&
          snd(snd(output@SR(j,i,l2))) = snd(snd(input@FI(i,j,l)))
.
Proof.
intro i j l.
split.
expand exec.
expand cond.
euf H0.
assert ( SR(j,i0,l0) <= FI(i,j,l) || SR(j,i0,l0) < FI(i,j,l)) <=>  SR(j,i0,l0) < FI(i,j,l).
case H1.
use H2.

project.
use uniqepk with vkI(i),vkI(i0).
exists l0.
depends I(i,j,l), FI(i,j,l).
by use sufcma with xor(ktilde3(i,j,l)@FI(i,j,l),snd(snd(input@FI(i,j,l)))), sid3(i,j,l)@FI(i,j,l), skR(j).

case    try find i2,j2,l2 such that KT1(i,j,l)@FI(i,j,l) = kt(j2,i2,l2)
    in k(j2,i2,l2) else decap(fst(snd(input@FI(i,j,l))),vkI(i)).
substeq (try find i2,j2,l2 such that KT1(i,j,l)@FI(i,j,l) = kt(j2,i2,l2)
       in k(j2,i2,l2) else decap(fst(snd(input@FI(i,j,l))),vkI(i))),
      k(j,i,l0).
by use uniqepk with vkI(i),vkI(i0).

exists l0.
depends I(i,j,l), FI(i,j,l).
by use sufcma with xor(ktilde3(i,j,l)@FI(i,j,l),snd(snd(input@FI(i,j,l)))), sid3(i,j,l)@FI(i,j,l), skR(j).

use uniqepk with vkI(i),vkI(i0).
by use H4 with i,j,l0.


project.
expand exec. expand cond.
depends I(i,j,l), FI(i,j,l).


assert ktilde2(j,i,l2)@SR(j,i,l2) = ktilde3(i,j,l)@FI(i,j,l).
expand output.
substeq snd(snd(input@FI(i,j,l))),   xor(ktilde2(j,i,l2)@SR(j,i,l2),
           sign(sid2(j,i,l2)@SR(j,i,l2),skR(j))).
assert sid2(j,i,l2)@SR(j,i,l2) = sid3(i,j,l)@FI(i,j,l).

use xorconcel with ktilde3(i,j,l)@FI(i,j,l), ktilde2(j,i,l2)@SR(j,i,l2),  sign(sid2(j,i,l2)@SR(j,i,l2),skR(j)).

substeq xor(ktilde3(i,j,l)@FI(i,j,l),
      xor(ktilde2(j,i,l2)@SR(j,i,l2),sign(sid2(j,i,l2)@SR(j,i,l2),skR(j)))),
      sign(sid2(j,i,l2)@SR(j,i,l2),skR(j)).
use rcheck with  sid2(j,i,l2)@SR(j,i,l2), sid3(i,j,l)@FI(i,j,l)   ,skR(j).


expand exec. expand cond.
depends I(i,j,l), FI(i,j,l).

case    try find i2,j2,l2 such that KT1(i,j,l)@FI(i,j,l) = kt(j2,i2,l2)
    in k(j2,i2,l2) else decap(fst(snd(input@FI(i,j,l))),vkI(i)).
substeq (try find i2,j2,l2 such that KT1(i,j,l)@FI(i,j,l) = kt(j2,i2,l2)
       in k(j2,i2,l2) else decap(fst(snd(input@FI(i,j,l))),vkI(i))),
      k(j,i,l2).
substeq  (try find i2,j2,l3 such that KT1(i,j,l)@FI(i,j,l) = kt(j2,i2,l3)
       in k(j2,i2,l3) else decap(fst(snd(input@FI(i,j,l))),vkI(i))),
      k(j,i,l2).


assert ktilde2(j,i,l2)@SR(j,i,l2) = ktilde3(i,j,l)@FI(i,j,l).
expand output.
substeq snd(snd(input@FI(i,j,l))),   xor(ktilde2(j,i,l2)@SR(j,i,l2),
           sign(sid2(j,i,l2)@SR(j,i,l2),skR(j))).
assert sid2(j,i,l2)@SR(j,i,l2) = sid3(i,j,l)@FI(i,j,l).

use xorconcel with ktilde3(i,j,l)@FI(i,j,l), ktilde2(j,i,l2)@SR(j,i,l2),  sign(sid2(j,i,l2)@SR(j,i,l2),skR(j)).

substeq xor(ktilde3(i,j,l)@FI(i,j,l),
      xor(ktilde2(j,i,l2)@SR(j,i,l2),sign(sid2(j,i,l2)@SR(j,i,l2),skR(j)))),
      sign(sid2(j,i,l2)@SR(j,i,l2),skR(j)).
use rcheck with  sid2(j,i,l2)@SR(j,i,l2), sid3(i,j,l)@FI(i,j,l)   ,skR(j).


use H0 with i,j,l.
Qed.

(* As I1 is the converse of FI, we also have freely that *)
axiom [Ideal] auth2 :  forall (i,j,l:index) ,
   happens(I1(i,j,l)) =>
        exec@I1(i,j,l) <=>
      exec@pred(I1(i,j,l)) &&
        not(exists (l2:index),
          I(i,j,l) < I1(i,j,l) &&
          SR(j,i,l2) < I1(i,j,l) &&
          input@SR(j,i,l2) =  output@I(i,j,l) &&
          fst(output@SR(j,i,l2)) = fst(input@I1(i,j,l)) &&
          fst(snd(output@SR(j,i,l2))) = fst(snd(input@I1(i,j,l))) &&
          snd(snd(output@SR(j,i,l2))) = snd(snd(input@I1(i,j,l))))
.


equiv [Ideal] step1.
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
          SR(j,i,l2) < FI(i,j,l) &&
          input@SR(j,i,l2) =  output@I(i,j,l) &&
          fst(output@SR(j,i,l2)) = fst(input@FI(i,j,l)) &&
          fst(snd(output@SR(j,i,l2))) = fst(snd(input@FI(i,j,l))) &&
          snd(snd(output@SR(j,i,l2))) = snd(snd(input@FI(i,j,l))).

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
          SR(j,i,l2) < I1(i,j,l) &&
          input@SR(j,i,l2) =  output@I(i,j,l) &&
          fst(output@SR(j,i,l2)) = fst(input@I1(i,j,l)) &&
          fst(snd(output@SR(j,i,l2))) = fst(snd(input@I1(i,j,l))) &&
          snd(snd(output@SR(j,i,l2))) = snd(snd(input@I1(i,j,l)))).
nosimpl(use auth2 with i,j,l); assumption.

fa 8. fa 9.
 fa 10. fadup 9.
Qed.
