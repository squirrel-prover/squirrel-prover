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

*********************************************split**********************************)
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

(* We prove the authentication on this system, and use it to prove that we can
indeed hide the key over the network. *)

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

axiom [Ideal] auth :  forall (i,j,l:index) ,
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
substeq (try find kl,kj,ki such that
         (skex = skex && (kj = j && ki = i && kl = l))
       in rndp(kl,kj,ki) else exct(skex,k(j,i,l))),
      exct(skex,k(j,i,l)).

case (try find kl,kj,ki such that (skex = skex && (kj = j && ki = i && kl = l))
 in rndp(kl,kj,ki) else exct(skex,k(j,i,l))).

substeq (try find kl0,kj0,ki0 such that
         (skex = skex && (kj0 = kj && ki0 = ki && kl0 = kl))
       in rndp(kl0,kj0,ki0) else exct(skex,k(kj,ki,kl))),
      rndp(kl,kj,ki).
by use H1 with kl,kj,ki.
by use H1 with l,j,i.

case    try find i2,j2,l2 such that
                    KT2(i,j,l)@FI(i,j,l) = kt(j2,i2,l2)
                  in
                    try find kl,kj,ki such that
                      (skex = skex && (kj = j2 && ki = i2 && kl = l2))
                    in rndp(kl,kj,ki) else exct(skex,k(j2,i2,l2))
                  else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i))).
substeq  (try find i2,j2,l2 such that KT2(i,j,l)@FI(i,j,l) = kt(j2,i2,l2)
       in
         try find kl,kj,ki such that
           (skex = skex && (kj = j2 && ki = i2 && kl = l2))
         in rndp(kl,kj,ki) else exct(skex,k(j2,i2,l2))
       else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i)))),
      try find kl,kj,ki such that
        (skex = skex && (kj = j2 && ki = i2 && kl = l2))
      in rndp(kl,kj,ki) else exct(skex,k(j2,i2,l2)).
substeq (try find i3,j3,l3 such that KT2(i,j,l)@FI(i,j,l) = kt(j3,i3,l3)
       in
         try find kl,kj,ki such that
           (skex = skex && (kj = j3 && ki = i3 && kl = l3))
         in rndp(kl,kj,ki) else exct(skex,k(j3,i3,l3))
       else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i)))),
      try find kl,kj,ki such that
        (skex = skex && (kj = j2 && ki = i2 && kl = l2))
      in rndp(kl,kj,ki) else exct(skex,k(j2,i2,l2)).

case   try find kl,kj,ki such that
                    (skex = skex && (kj = j2 && ki = i2 && kl = l2))
                  in rndp(kl,kj,ki) else exct(skex,k(j2,i2,l2)).

substeq  (try find kl0,kj0,ki0 such that
         (skex = skex && (kj0 = kj && ki0 = ki && kl0 = kl))
       in rndp(kl0,kj0,ki0) else exct(skex,k(kj,ki,kl))),
      rndp(kl,kj,ki).

case  try find i3,j3,l3 such that
                    KT2(i,j,l)@FI(i,j,l) = kt(j3,i3,l3)
                  in rndp(l3,j3,i3)
                  else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i))).
substeq  (try find i3,j3,l3 such that KT2(i,j,l)@FI(i,j,l) = kt(j3,i3,l3)
       in rndp(l3,j3,i3)
       else exct(skex,decap(fst(snd(input@FI(i,j,l))),vkI(i)))),
      rndp(kl,kj,ki).
by use H1 with ki,kj,kl.
by use H1 with l2,j2,i2.


forceuse auth with i,j,l. use H2.
use H1 with i,j,l2.
expand output.

substeq fst(input@FI(i,j,l)), CT2(j,i,l2)@SR(j,i,l2).
forceuse fstpair with CT2(j,i,l2)@SR(j,i,l2),
         diff(
           <C2(j,i,l2)@SR(j,i,l2),
            xor(xor(F2(sid4(j,i,l2)@SR(j,i,l2),
                    try find kl,kj,ki such that
                      (skex = skex && (kj = j && ki = i && kl = l2))
                    in rndp(kl,kj,ki) else exct(skex,k(j,i,l2))),
                F2(sid4(j,i,l2)@SR(j,i,l2),K10(j,i,l2)@SR(j,i,l2))),
            sign(sid4(j,i,l2)@SR(j,i,l2),skR(j)))>,
           <C2(j,i,l2)@SR(j,i,l2),
            xor(xor(F2(sid4(j,i,l2)@SR(j,i,l2),rndp(l2,j,i)),
                F2(sid4(j,i,l2)@SR(j,i,l2),K10(j,i,l2)@SR(j,i,l2))),
            sign(sid4(j,i,l2)@SR(j,i,l2),skR(j)))>).
substeq fst(
        <CT2(j,i,l2)@SR(j,i,l2),
         diff(
           <C2(j,i,l2)@SR(j,i,l2),
            xor(xor(F2(sid4(j,i,l2)@SR(j,i,l2),
                    try find kl,kj,ki such that
                      (skex = skex && (kj = j && ki = i && kl = l2))
                    in rndp(kl,kj,ki) else exct(skex,k(j,i,l2))),
                F2(sid4(j,i,l2)@SR(j,i,l2),K10(j,i,l2)@SR(j,i,l2))),
            sign(sid4(j,i,l2)@SR(j,i,l2),skR(j)))>,
           <C2(j,i,l2)@SR(j,i,l2),
            xor(xor(F2(sid4(j,i,l2)@SR(j,i,l2),rndp(l2,j,i)),
                F2(sid4(j,i,l2)@SR(j,i,l2),K10(j,i,l2)@SR(j,i,l2))),
            sign(sid4(j,i,l2)@SR(j,i,l2),skR(j)))>)>),
      CT2(j,i,l2)@SR(j,i,l2).

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

substeq  (try find ml2,ml3,mj0,mi0 such that
         (sid7(i,j,l)@FI(i,j,l) =
          <epk(vkI(mi0)),
           <epk(vkR(mj0)),
            <epk(dkt(mi0,mj0,ml2)),
             <encap(rnd(mj0,mi0,ml3),rk(mj0,mi0,ml3),epk(vkI(mi0))),
              encap(kt(mj0,mi0,ml3),rkt(mj0,mi0,ml3),epk(dkt(mi0,mj0,ml2)))>>>> &&
          (ml3 = l0 && mj0 = mj && mi0 = mi))
       in ideal(ml2,ml3,mj0,mi0)
       else F1(sid7(i,j,l)@FI(i,j,l),rndp(l0,mj,mi))),
      ideal(ml2,l0,mj,mi).

substeq  (try find ml3,ml4,mj0,mi0 such that
         (sid7(i,j,l)@FI(i,j,l) =
          <epk(vkI(mi0)),
           <epk(vkR(mj0)),
            <epk(dkt(mi0,mj0,ml3)),
             <encap(rnd(mj0,mi0,ml4),rk(mj0,mi0,ml4),epk(vkI(mi0))),
              encap(kt(mj0,mi0,ml4),rkt(mj0,mi0,ml4),epk(dkt(mi0,mj0,ml3)))>>>> &&
          (ml4 = l0 && mj0 = mj && mi0 = mi))
       in ideal(ml3,ml4,mj0,mi0)
       else F1(sid7(i,j,l)@FI(i,j,l),rndp(l0,mj,mi))),
      ideal(ml2,l0,mj,mi).


nosimpl(forceuse auth with i,j,l).
use H1.  use H1.


forceuse uniqepk with dkt(i,j,l), dkt(i,j,ml2).
simpl.

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
substeq (try find ml2,ml3,mj0,mi0 such that
        (sid6(mj,mi,l)@FR(mj,mi,l) =
         <epk(vkI(mi0)),
          <epk(vkR(mj0)),
           <epk(dkt(mi0,mj0,ml2)),
            <encap(rnd(mj0,mi0,ml3),rk(mj0,mi0,ml3),epk(vkI(mi0))),
             encap(kt(mj0,mi0,ml3),rkt(mj0,mi0,ml3),epk(dkt(mi0,mj0,ml2)))>>>> &&
         (ml3 = l && mj0 = mj && mi0 = mi))
      in ideal(ml2,ml3,mj0,mi0)
      else F1(sid6(mj,mi,l)@FR(mj,mi,l),rndp(l,mj,mi))),
     ideal(ml2,l,mj,mi).
substeq  (try find ml3,ml4,mj0,mi0 such that
        (sid6(mj,mi,l)@FR(mj,mi,l) =
         <epk(vkI(mi0)),
          <epk(vkR(mj0)),
           <epk(dkt(mi0,mj0,ml3)),
            <encap(rnd(mj0,mi0,ml4),rk(mj0,mi0,ml4),epk(vkI(mi0))),
             encap(kt(mj0,mi0,ml4),rkt(mj0,mi0,ml4),epk(dkt(mi0,mj0,ml3)))>>>> &&
         (ml4 = l && mj0 = mj && mi0 = mi))
      in ideal(ml3,ml4,mj0,mi0)
      else F1(sid6(mj,mi,l)@FR(mj,mi,l),rndp(l,mj,mi))),
     ideal(ml2,l,mj,mi).

case try find l2 such that input@SR(mj,mi,l) = epk(dkt(mi,mj,l2))
in ideal(l2,l,mj,mi) else F1(sid6(mj,mi,l)@FR(mj,mi,l),rndp(l,mj,mi)).
substeq  (try find l2 such that input@SR(mj,mi,l) = epk(dkt(mi,mj,l2))
       in ideal(l2,l,mj,mi) else F1(sid6(mj,mi,l)@FR(mj,mi,l),rndp(l,mj,mi))),
      ideal(l2,l,mj,mi).
substeq  (try find l3 such that input@SR(mj,mi,l) = epk(dkt(mi,mj,l3))
       in ideal(l3,l,mj,mi) else F1(sid6(mj,mi,l)@FR(mj,mi,l),rndp(l,mj,mi))),
      ideal(l2,l,mj,mi).
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
