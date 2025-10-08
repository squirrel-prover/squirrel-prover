(** 
#Yahalom
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb : nonce
    1, 2, 3 : tag

    A -> B : A, Na
    B -> S : B, Nb, {1, A, Na}_Kbs
    S -> A : Nb, {2, B, K, Na}_Kas, {3, A, B K, Nb}_Kbs
    A -> B : {3, A, B, K, Nb}_Kbs
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
abstract tag3: message.
axiom[any] cst12_diff : tag1 <> tag2.
hint rewrite cst12_diff.
axiom[any] cst13_diff : tag1 <> tag3.
hint rewrite cst13_diff.
axiom[any] cst23_diff : tag2 <> tag3.
hint rewrite cst23_diff.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Cst tag1 * Low
                                  + Cst tag2 * (Cst id * (High * Low))
                                  + Cst tag3 * (Cst id * (Low * (High * Low)))
                                  + Cst tag2 * (Cst idD *  Low)
                                  + Cst tag3 * (Cst idD * Low)].

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
name Rb : index * index * index -> message, Rand.
name Rsa : index * index * index -> message, Rand.
name Rsb : index * index * index -> message, Rand.

name RDb : index * index * index -> message, Rand.
name RHDsa : index * index * index -> message, Rand.
name RHDsb : index * index * index -> message, Low.

name RDHsa : index * index * index -> message, Low.
name RDHsb : index * index * index -> message, Rand.


process InitH(i,j,k:index)=
  IH1: out(c, <id(i),Na(i,j,k)>);
  IH2: in(c,x);
       let mIH = dec(fst(snd(x)),Ks(i)) in
       let kI = fst(snd(snd(mIH))) in
       if mIH <> fail 
       && fst(mIH) = tag2
       && fst(snd(mIH)) = id(j)
       && snd(snd(snd(mIH))) = Na(i,j,k)
       then out(c, snd(snd(x))).

process InitD(i,j,k:index)=
  ID1: out(c, <id(i),NDa(i,j,k)>);
  ID2: in(c,x);
       let mID = dec(fst(snd(x)),Ks(i)) in  
       if mID <> fail 
       && fst(mID) = tag2
       && fst(snd(mID)) = idD(j)
       && snd(snd(snd(mID))) = NDa(i,j,k)
       then out(c, snd(snd(x))).

process ServerHH(i,j,k:index)=
  SHH: in(c, x);
       let mSHH = dec(snd(snd(x)),Ks(j)) in
       if fst(x) = id(j)
       && mSHH <> fail
       && fst(mSHH) = tag1
       && fst(snd(mSHH)) = id(i)
       then out(c, <fst(snd(x)), 
                   <enc(<tag2,<id(j),<K(i,j,k),snd(snd(snd(mSHH)))>>>, Rsa(i,j,k),Ks(i)),
                    enc(<tag3,<id(i),<id(j),<K(i,j,k),fst(snd(x))>>>>,Rsb(i,j,k),Ks(j))>>).

process ServerHD(i,j,k:index)=
  SHD: in(c, x);
       let mSHD = dec(snd(snd(x)),KDs(j)) in
       if fst(x) = idD(j) 
       && mSHD <> fail
       && fst(mSHD) = tag1
       && fst(snd(mSHD)) = id(i)
       then out(c, <fst(snd(x)), 
                   <enc(<tag2,<idD(j),<KHD(i,j,k),snd(snd(snd(mSHD)))>>>, RHDsa(i,j,k),Ks(i)),
                    enc(<tag3,<id(i),<idD(j),<KHD(i,j,k),fst(snd(x))>>>>,RHDsb(i,j,k),KDs(j))>>).

process ServerDH(i,j,k:index)=
  SDH: in(c, x);
       let mSDH = dec(snd(snd(x)),Ks(j)) in
       if fst(x) = id(j) 
       && mSDH <> fail
       && fst(mSDH) = tag1
       && fst(snd(mSDH)) = idD(i)
       then out(c, <fst(snd(x)), 
                   <enc(<tag2,<id(j),<KDH(i,j,k),snd(snd(snd(mSDH)))>>>, RDHsa(i,j,k),KDs(i)),
                    enc(<tag3,<idD(i),<id(j),<KDH(i,j,k),fst(snd(x))>>>>,RDHsb(i,j,k),Ks(j))>>).

process RespH(i,j,k:index)=
  RH1: in(c, x);
       if fst(x) = id(i)
       then out(c,<id(j), <Nb(i,j,k), enc(<tag1, <id(i), snd(x)>>, Rb(i,j,k),Ks(j))>>);
  RH2: in(c,y);
       let mRH = dec(y,Ks(j)) in
       let kR = fst(snd(snd(snd(mRH)))) in
       if mRH <> fail 
       && fst(mRH) = tag3
       && fst(snd(mRH)) = id(i)
       && fst(snd(snd(mRH))) = id(j)
       && snd(snd(snd(mRH))) = Nb(i,j,k)
       then out(c,empty).

process RespD(i,j,k:index)=
  RD1: in(c, x);
       if fst(x) = idD(i)
       then out(c,<id(j), <NDb(i,j,k), enc(<tag1, <idD(i), snd(x)>>, RDb(i,j,k),Ks(j))>>);
  RD2: in(c,y);
       let mRD = dec(y,Ks(j)) in 
       if mRD <> fail 
       && fst(mRD) = tag3
       && fst(snd(mRD)) = id(i)
       && fst(snd(snd(mRD))) = id(j)
       && snd(snd(snd(mRD))) = NDb(i,j,k)
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

