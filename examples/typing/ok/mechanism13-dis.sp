(** 
#Mechanism 13 - ISO 11770
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb : nonce
    1, 2, 3 : tag

    B -> A : Nb
    A -> S : {1, Na, Nb, B, K}_Kas
    S -> A : {2, Na, Nb, B}_Kas,  {3, Nb, K, A}_Kbs
    A -> B : {3, Nb, K, A}_Kbs
**)

set securityTypes = true.

include Logic.

channel c.

senc enc,dec.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.
(* idD(i) is the identifier of dishonest agent i *)
abstract idD : index -> message.
axiom[any] cst_id_idD : forall i j, id i <> idD j <: Real.z.
hint rewrite cst_id_idD.

(* tag *)
abstract tag1: message. 
abstract tag2: message. 
abstract tag3: message.
axiom[any] cst12_diff : tag1 <> tag2 <: Real.z.
hint rewrite cst12_diff.
axiom[any] cst13_diff : tag1 <> tag3 <: Real.z.
hint rewrite cst13_diff.
axiom[any] cst23_diff : tag2 <> tag3 <: Real.z.
hint rewrite cst23_diff.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Cst tag1 * (Low * (Low * (Cst id * High)))
                                  + Cst tag2 * Low
                                  + Cst tag3 * (Low * (High * Cst id))
                                  + Cst tag1 * (Low * (Low * (Cst idD * Low)))
                                  + Cst tag3 * (Low * (Low * Cst idD))].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.
name Na: index * index * index -> message, Low.
name Nb: index * index * index -> message, Low.
name Kfresh: message, High.

(* KDs(i) long-term key shared between idD(i) and the server *)
name KDs : index -> message, Low.

(* session key shared with a dishonest agent *)
name KD: index * index * index -> message, Low.

name NDa: index * index * index -> message, Low.
name NDb: index * index * index -> message, Low.

(* Randoms used in encryption *)
name Ra : index * index * index -> message, Rand.
name RDa : index * index * index -> message, Rand.


name Rsa : index * index * index -> message, Rand.
name Rsb : index * index * index -> message, Rand.

name RHDsa : index * index * index -> message, Rand.
name RHDsb : index * index * index -> message, Low.

name RDHsa : index * index * index -> message, Low.
name RDHsb : index * index * index -> message, Rand.
 
process InitH(i,j,k:index)=
  IH1: in(c,x); out(c, enc(<tag1, <Na(i,j,k), <x, <id(j), K(i,j,k)>>>>,Ra(i,j,k),Ks(i)));
  IH2: in(c,y);
       let mIH = dec(fst(y),Ks(i)) in
       if mIH <> fail
       && fst(mIH) = tag2
       && fst(snd(mIH)) = Na(i,j,k)
       && fst(snd(snd(mIH))) = x
       && snd(snd(snd(mIH))) = id(j)
       then out(c, snd(y)).

process InitD(i,j,k:index)=
  ID1: in(c,x); out(c, enc(<tag1, <NDa(i,j,k), <x, <idD(j), KD(i,j,k)>>>>,RDa(i,j,k),Ks(i)));
  ID2: in(c,y);
       let mID = dec(fst(y),Ks(i)) in
       if mID <> fail 
       && fst(mID) = tag2
       && fst(snd(mID)) = NDa(i,j,k)
       && fst(snd(snd(mID))) = x
       && snd(snd(snd(mID))) = idD(j)
       then out(c, snd(y)).

process ServerHH(i,j,k:index)=
  SHH: in(c, x);
       let mSHH = dec(x,Ks(i)) in
       let kS = snd(snd(snd(snd(mSHH)))) in
       if mSHH <> fail
       && fst(mSHH) = tag1
       && fst(snd(snd(snd(mSHH)))) = id(j)
       then out(c, <enc(<tag2,<fst(snd(mSHH)),<fst(snd(snd(mSHH))),id(j)>>>,Rsa(i,j,k),Ks(i)),
                    enc(<tag3,<fst(snd(snd(mSHH))), <snd(snd(snd(snd(mSHH)))),id(i)>>>, Rsb(i,j,k),Ks(j))>).

process ServerHD(i,j,k:index)=
  SHD: in(c, x);
       let mSHD = dec(x,Ks(i)) in
       if mSHD <> fail 
       && fst(mSHD) = tag1
       && fst(snd(snd(snd(mSHD)))) = idD(j)
       then out(c, <enc(<tag2,<fst(snd(mSHD)),<fst(snd(snd(mSHD))),idD(j)>>>,RHDsa(i,j,k),Ks(i)),
                    enc(<tag3,<fst(snd(snd(mSHD))), <snd(snd(snd(snd(mSHD)))),id(i)>>>, RHDsb(i,j,k),KDs(j))>).


process ServerDH(i,j,k:index)=
  SDH: in(c, x);
       let mSDH = dec(x,KDs(i)) in
       if mSDH <> fail 
       && fst(mSDH) = tag1
       && fst(snd(snd(snd(mSDH)))) = id(j)
       then out(c, <enc(<tag2,<fst(snd(mSDH)),<fst(snd(snd(mSDH))),idD(j)>>>,RDHsa(i,j,k),KDs(i)),
                    enc(<tag3,<fst(snd(snd(mSDH))), <snd(snd(snd(snd(mSDH)))),idD(i)>>>, RDHsb(i,j,k),Ks(j))>).

process RespH(i,j,k:index)=
  RH1: out(c, Nb(i,j,k));
  RH2: in(c,y); 
       let mRH = dec(y,Ks(j)) in
       let kR = fst(snd(snd(mRH))) in
       if mRH <> fail 
       && fst(mRH) = tag3
       && fst(snd(mRH)) = Nb(i,j,k)
       && snd(snd(snd(mRH))) = id(i)
       then out(c,empty).

process RespD(i,j,k:index)=
  RD1: out(c, NDb(i,j,k));
  RD2: in(c,y);
       let mRD = dec(y,Ks(j)) in
       if mRD <> fail 
       && fst(mRD) = tag3
       && fst(snd(mRD)) = NDb(i,j,k)
       && snd(snd(snd(mRD))) = idD(i)
       then out(c,empty).

system ( !_i !_j !_k (InitH(i,j,k) | ServerHH(i,j,k) | RespH(i,j,k)   | 
                      InitD(i,j,k) | ServerHD(i,j,k) | 
                                     ServerDH(i,j,k)| RespD(i,j,k) 
)).
Proof.
  auto.
Qed.

(* secrecy from the point of view of the initiator *)
 lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) =>  att(frame@tau) <> K(i,j,k).
Proof.
  intro *. 
  typing Meq. 
Qed.

(* secrecy from the point of view of the server *)
lemma key_secrecy_server: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) =>  tau >= SHH(i,j,k) => 
   att(frame@tau) <> 
   if cond@SHH(i,j,k) then kS@SHH(i,j,k) else Kfresh.
Proof.
  intro *. 
  expandall.
  by typing Meq.
Qed.

(* secrecy from the point of view of the responder *)
lemma key_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= RH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@RH2(i,j,k) then kR@RH2(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall. 
  by typing Meq.
Qed.

