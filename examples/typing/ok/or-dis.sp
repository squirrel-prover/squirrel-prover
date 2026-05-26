(** 
#Otways-Rees 
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb, M : nonce
    req, rep : tag
    A -> B : M, A, B, {req, Na, M, A, B}_Kas
    B -> S : A, B, {req, Na, M, A, B}_Kas, {req, Nb, M, A, B}_Kbs
    S -> B : {rep, Na, K}_Kas, {rep, Nb, K}_Kbs
    B -> A : {rep, Na, K}Kas
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
abstract req: message. 
abstract rep: message. 
axiom[any] cst_diff1 : rep <> req <: Real.z.
hint rewrite cst_diff1.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, 
Cst req * (High * (Low * (Cst id * Cst id)))
+ Cst req * (Low * (Low * (Cst id * Cst idD))) 
+ Cst req * (Low * (Low * (Cst idD * Cst id))) 
+ Cst rep * (High * High)
+ Cst rep * (Low * Low)].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.
name Na: index * index * index -> message, High.
name Nb: index * index * index -> message, High.
name M: index * index * index -> message, Low.
name Kfresh: message, High.

(* KDs(i) long-term key shared between idD(i) and the server *)
name KDs : index -> message, Low.

(* session key shared with a dishonest agent *)
name KHD: index * index * index -> message, Low.
name KDH: index * index * index -> message, Low.

name MD: index * index * index -> message, Low.
name NDa: index * index * index -> message, Low.
name NDb: index * index * index -> message, Low.

(* Randoms used in encryption *)
name Ra : index * index * index -> message, Rand.
name RDa : index * index * index -> message, Rand.

name Rb : index * index * index -> message, Rand.
name RDb : index * index * index -> message, Rand.

name Rsa : index * index * index -> message, Rand.
name Rsb : index * index * index -> message, Rand.

name RHDsa : index * index * index -> message, Rand.
name RHDsb : index * index * index -> message, Low.

name RDHsa : index * index * index -> message, Low.
name RDHsb : index * index * index -> message, Rand.

process InitH(i,j,k:index)=
  IH1: out(c, <M(i,j,k), <id(i),<id(j),
               enc(<req, <Na(i,j,k), <M(i,j,k), <id(i),id(j)>>>>, Ra(i,j,k),Ks(i))>>>);
  IH2: in(c,x);
       let mIH = dec(x, Ks(i)) in
       let kI = snd(snd(mIH)) in
       if mIH <> fail && fst(mIH) = rep && fst(snd(mIH)) = Na(i,j,k)
       then out(c, empty).

process InitD(i,j,k:index)=
  ID1: out(c, <MD(i,j,k), <id(i),<idD(j),
               enc(<req, <NDa(i,j,k), <MD(i,j,k), <id(i),idD(j)>>>>, RDa(i,j,k),Ks(i))>>>);
  ID2: in(c,x);  
       let mID = dec(x,Ks(i)) in
       if mID <> fail && fst(mID) = rep && fst(snd(mID)) = NDa(i,j,k)
       then out(c, empty).

process ServerHH(i,j,k:index)=
  SHH: in(c, x);
       let mSAHH = dec(fst(snd(snd(x))),Ks(i)) in
       let mSBHH = dec(snd(snd(snd(x))),Ks(j)) in
       if fst(x) = id(i) && fst(snd(x)) = id(j) && mSAHH <> fail && mSBHH <> fail
       && fst(mSAHH) = req && fst(mSBHH) = req
       && fst(snd(snd(snd(mSAHH)))) = id(i) &&  snd(snd(snd(snd(mSAHH)))) = id(j) 
       && fst(snd(snd(snd(mSBHH)))) = id(i) &&  snd(snd(snd(snd(mSBHH)))) = id(j)
       && fst(snd(snd(mSAHH))) = fst(snd(snd(mSBHH)))
       then out(c, <enc(<rep,<fst(snd(mSAHH)), K(i,j,k)>>, Rsa(i,j,k), Ks(i)),
                    enc(<rep,<fst(snd(mSBHH)), K(i,j,k)>>, Rsb(i,j,k), Ks(j))>).

process ServerHD(i,j,k:index)=
  SHD: in(c, x);
       let mSAHD = dec(fst(snd(snd(x))),Ks(i)) in
       let mSBHD = dec(snd(snd(snd(x))),KDs(j)) in
       if fst(x) = id(i) && fst(snd(x)) = idD(j) && mSAHD <> fail && mSBHD <> fail
       && fst(mSAHD) = req && fst(mSBHD) = req
       && fst(snd(snd(snd(mSAHD)))) = id(i) &&  snd(snd(snd(snd(mSAHD)))) = idD(j) 
       && fst(snd(snd(snd(mSBHD)))) = id(i) &&  snd(snd(snd(snd(mSBHD)))) = idD(j)
       && fst(snd(snd(mSAHD))) = fst(snd(snd(mSBHD)))
       then out(c, <enc(<rep,<fst(snd(mSAHD)), KHD(i,j,k)>>, RHDsa(i,j,k), Ks(i)),
                    enc(<rep,<fst(snd(mSBHD)), KHD(i,j,k)>>, RHDsb(i,j,k), KDs(j))>).

process ServerDH(i,j,k:index)=
  SDH: in(c, x);
       let mSADH = dec(fst(snd(snd(x))),KDs(i)) in
       let mSBDH = dec(snd(snd(snd(x))),Ks(j)) in
       if fst(x) = idD(i) && fst(snd(x)) = id(j) && mSADH <> fail && mSBDH <> fail
       && fst(mSADH) = req && fst(mSBDH) = req
       && fst(snd(snd(snd(mSADH)))) = idD(i) &&  snd(snd(snd(snd(mSADH)))) = id(j) 
       && fst(snd(snd(snd(mSBDH)))) = idD(i) &&  snd(snd(snd(snd(mSBDH)))) = id(j)
       && fst(snd(snd(mSADH))) = fst(snd(snd(mSBDH)))
       then out(c, <enc(<rep,<fst(snd(mSADH)), KDH(i,j,k)>>, RDHsa(i,j,k), KDs(i)),
                    enc(<rep,<fst(snd(mSBDH)), KDH(i,j,k)>>, RDHsb(i,j,k), Ks(j))>).

process RespH(i,j,k:index)=
  RH1: in(c, x);
       if fst(snd(snd(x))) = id(j)
       then out(c,<id(i), <id(j), <snd(snd(snd(x))), enc(<req, <Nb(i,j,k), <fst(x), <id(i),id(j)>>>>, Rb(i,j,k),Ks(j))>>>);
  RH2: in(c,y); 
       let mRH = dec(snd(y),Ks(j)) in
       let kR = snd(snd(mRH)) in
       if mRH <> fail && fst(mRH) = rep && fst(snd(mRH)) = Nb(i,j,k)
       then out(c,fst(y)).

process RespD(i,j,k:index)=
  RD1: in(c, x);
       if fst(snd(snd(x))) = id(j)
       then out(c,<idD(i), <id(j), <snd(snd(snd(x))), enc(<req, <NDb(i,j,k), <fst(x), <idD(i),id(j)>>>>, RDb(i,j,k),Ks(j))>>>);
  RD2: in(c,y); 
       let mRD = dec(snd(y),Ks(j)) in
       if mRD <> fail && fst(mRD) = rep && fst(snd(mRD)) = NDb(i,j,k)
       then out(c,fst(y)).

system ( !_i !_j !_k (InitH(i,j,k) | ServerHH(i,j,k) | RespH(i,j,k)  | 
                      InitD(i,j,k) | ServerHD(i,j,k) | 
                                     ServerDH(i,j,k) | RespD(i,j,k)
)).
Proof.
  auto.
Qed.


(* secrecy from the point of view of the initiator *)
lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= IH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@IH2(i,j,k) then kI@IH2(i,j,k) else Kfresh.
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
   if cond@RH2(i,j,k) then kR@RH2(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall. 
  by typing Meq.
Qed.

