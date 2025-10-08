(** 
#Mechanism 9
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb : nonce
    1, 2 : tag

    B -> A : Nb
    A -> S : Na, Nb, B
    S -> A : {1, Na, K, B}_Kas, {2, Nb, K, A}_Kbs
    A -> B : {2, Nb, K, A}_Kbs
**)

set securityTypes = true.

include Logic.

channel c.

senc enc,dec.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.
(* idD(i) is the identifier of dishonest agent i *)
abstract idD : index -> message.
axiom[any] cst_id_idD : forall i j, id i <> idD j.
hint rewrite cst_id_idD.

(* tag *)
abstract tag1: message. 
abstract tag2: message. 
axiom[any] cst_diff1 : tag1 <> tag2.
hint rewrite cst_diff1.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Cst tag1 * (Low * (High * Cst id))
                                  + Cst tag2 * (Low * (High * Cst id))
                                  + Cst tag1 * (Low * (Low * Cst idD))
                                  + Cst tag2 * (Low * (Low * Cst idD))].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.
name Na: index * index * index -> message, Low.
name Nb: index * index * index -> message, Low.
name Kfresh: message, High.

(* KDs(i) long-term key shared between idD(i) and the server *)
name KDs : index -> message, Low.

(* session key shared with a dishonest agent *)
name KHD: index * index * index -> message, Low.
name KDH: index * index * index -> message, Low.

name NDa: index * index * index -> message, Low.
name NDb: index * index * index -> message, Low.

(* Randoms used in encryption *)
name Rsa : index * index * index -> message, Rand.
name Rsb : index * index * index -> message, Rand.

name RHDsa : index * index * index -> message, Rand.
name RHDsb : index * index * index -> message, Low.

name RDHsa : index * index * index -> message, Low.
name RDHsb : index * index * index -> message, Rand.


process InitH(i,j,k:index)=
  IH1: in(c,x); out(c, <Na(i,j,k), <x, id(j)>>);
  IH2: in(c,y);
       let mIH = dec(fst(y),Ks(i)) in
       let kI = fst(snd(snd(mIH))) in
       if mIH <> fail 
       && fst(mIH) = tag1
       && fst(snd(mIH)) = Na(i,j,k)
       && snd(snd(snd(mIH))) = id(j)
       then out(c, snd(y)).

process InitD(i,j,k:index)=
  ID1: in(c,x); out(c, <NDa(i,j,k), <x, idD(j)>>);
  ID2: in(c,y);
       let mID = dec(fst(y),Ks(i)) in
       if mID <> fail 
       && fst(mID) = tag1
       && fst(snd(mID)) = NDa(i,j,k)
       && snd(snd(snd(mID))) = idD(j)
       then out(c, snd(y)).

process ServerHH(i,j,k:index)=
  SHH: in(c, x);
       if snd(snd(x)) = id(j) 
       then out(c, <enc(<tag1,<fst(x), <K(i,j,k),id(j)>>>, Rsa(i,j,k),Ks(i)),
                    enc(<tag2,<fst(snd(x)), <K(i,j,k),id(i)>>>,Rsb(i,j,k),Ks(j))>).

process ServerHD(i,j,k:index)=
  SHD: in(c, x);
       if snd(snd(x)) = idD(j) 
       then out(c, <enc(<tag1,<fst(x), <KHD(i,j,k),idD(j)>>>, RHDsa(i,j,k),Ks(i)),
                    enc(<tag2,<fst(snd(x)), <KHD(i,j,k),id(i)>>>,RHDsb(i,j,k),KDs(j))>).

process ServerDH(i,j,k:index)=
  SDH: in(c, x);
       if snd(snd(x)) = id(j) 
       then out(c, <enc(<tag1,<fst(x), <KDH(i,j,k),id(j)>>>, RDHsa(i,j,k),KDs(i)),
                    enc(<tag2,<fst(snd(x)), <KDH(i,j,k),idD(i)>>>,RDHsb(i,j,k),Ks(j))>).

process RespH(i,j,k:index)=
  RH1: out(c, Nb(i,j,k));
  RH2: in(c,y); 
       let mRH = dec(y,Ks(j)) in
       let kR = fst(snd(snd(mRH))) in
       if mRH <> fail 
       && fst(mRH) = tag2
       && fst(snd(mRH)) = Nb(i,j,k)
       && snd(snd(snd(mRH))) = id(i)
       then out(c,empty).

process RespD(i,j,k:index)=
  RD1: out(c, NDb(i,j,k));
  RD2: in(c,y); 
       let mRD = dec(y,Ks(j)) in
       if mRD <> fail 
       && fst(mRD) = tag2
       && fst(snd(mRD)) = NDb(i,j,k)
       && snd(snd(snd(mRD))) = idD(i)
       then out(c,empty).

system ( !_i !_j !_k (InitH(i,j,k) | ServerHH(i,j,k) | RespH(i,j,k)  | 
                      InitD(i,j,k) | ServerHD(i,j,k) | 
                                     ServerDH(i,j,k)| RespD(i,j,k) 
)).
Proof.
  auto.
Qed.

(* secrecy from the point of view of the initiator *)
 lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= IH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@IH2(i,j,k) then kI i j k@IH2(i,j,k) else Kfresh.
Proof.
  intro *. 
  expandall. 
  by typing Meq. 
Qed.

(* secrecy from the point of view of the server *)
lemma key_secrecy_server: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) =>  att(frame@tau) <> K(i,j,k).
Proof.
  intro *. 
  typing Meq.
Qed.

(* secrecy from the point of view of the responder *)
lemma key_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= RH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@RH2(i,j,k) then kR i j k@RH2(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall.
  by typing Meq.
Qed.

