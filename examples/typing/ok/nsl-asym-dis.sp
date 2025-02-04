(** 
#Needham-Schroeder-Lowe (asymmetric)
    A, B : principal
    Kas, Kbs, K : symkey
    Na : nonce

    A -> B : {1, Na, A}_pubB
    B -> A : {2, Na, Nb, B}_pubA
    A -> B : {3, Nb}_pubB
**)

set securityTypes = true.

include Logic.

channel c.

aenc enc,dec,pk.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.
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

(* sKey(i) long-term private key of (honest) agent id(i) *)
name sKey : index -> message, AK[enc, Cst tag1 * (High * Cst id)
                                    + Cst tag2 * (Msg * (High * Cst id))
                                    + Cst tag3 * High
                                    + Low].

name sKeyD: index -> message, Low.

name Na: index * index  * index -> message, High.
name Nb: index * index * index -> message, High.
name NDa: index * index  * index -> message, Low.
name NDb: index * index * index -> message, Low.
name Kfresh: message, High.

(* Randoms used in encryption *)
name Ra1 : index * index * index -> message, Rand.
name Rb : index * index * index -> message, Rand.
name Ra2 : index * index * index -> message, Rand.
name RDa1 : index * index * index -> message, Low.
name RDb : index * index * index -> message, Low.
name RDa2 : index * index * index -> message, Low.

process InitH(i,j,k:index)=
  IH1: out(c, enc(<tag1, <Na(i,j,k),id(i)>>,Ra1(i,j,k),pk(sKey(j))));
  IH2: in(c,x);  
       let mIH = dec(x,sKey(i)) in
       let tIH = fst(mIH) in
       let naIH = fst(snd(mIH)) in
       let nbIH = fst(snd(snd(mIH))) in
       let identIH = snd(snd(snd(mIH))) in
       if mIH <> fail && tIH = tag2 && naIH = Na(i,j,k) && identIH = id(j)
       then out(c, enc(<tag3, nbIH>, Ra2(i,j,k), pk(sKey(j)))). 

process InitD(i,j,k:index)=
  ID1: out(c, enc(<tag1, <NDa(i,j,k),id(i)>>,RDa1(i,j,k),pk(sKeyD(j))));
  ID2: in(c,x); 
       let mID = dec(x,sKey(i)) in
       let tID = fst(mID) in
       let naID = fst(snd(mID)) in
       let nbID = fst(snd(snd(mID))) in
       let identID = snd(snd(snd(mID))) in
       if mID  <> fail  && tID = tag2 && naID = NDa(i,j,k) && identID = idD(j)
       then out(c, enc(<tag3, nbID>, RDa2(i,j,k), pk(sKeyD(j)))). 

process RespH(i,j,k:index)=
  RH1: in(c, x);
       let mRH = dec(x,sKey(j)) in
       let tRH = fst(mRH) in
       let naRH = fst(snd(mRH)) in
       let identRH = snd(snd(mRH)) in
       if mRH <> fail  && tRH = tag1 && identRH = id(i) 
       then out(c,enc(<tag2, < naRH , <Nb(i,j,k), id(j)>>>, Rb(i,j,k), pk(sKey(i))));  
  RH2: in(c,y);
       if dec(y,sKey(j)) <> fail && fst(dec(y,sKey(j))) = tag3 && snd(dec(y,sKey(j))) = Nb(i,j,k) 
       then out(c,empty). 

process RespD(i,j,k:index)=
  RD1: in(c, x);
       let mRD = dec(x,sKey(j)) in
       let tRD = fst(mRD) in
       let naRD = fst(snd(mRD)) in
       let identRD = snd(snd(mRD)) in
       if mRD <> fail  && tRD = tag1 && identRD = idD(i) 
       then out(c,enc(<tag2, < naRD, <NDb(i,j,k), id(j)>>>, RDb(i,j,k), pk(sKeyD(i))));  
  RD2: in(c,y);
       if dec(y,sKey(j)) <> fail && fst(dec(y,sKey(j))) = tag3 && snd(dec(y,sKey(j))) = NDb(i,j,k) 
       then out(c,empty). 

system ( !_i !_j !_k out(c,pk(sKey(i))); out(c,pk(sKey(j)));(  InitD(i,j,k)  | RespD(i,j,k)  |  InitH(i,j,k)  | RespH(i,j,k)  )).
Proof.
  auto.
Qed.

(* secrecy from the point of view of the responder *)
lemma Nb_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => att(frame@tau) <> Nb(i,j,k).
Proof.
  intro *.
  typing Meq.
Qed.


(* secrecy from the point of view of the initiator *)
lemma Nb_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= IH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@IH2(i,j,k) then (nbIH i j k)@IH2(i,j,k) else Kfresh.
Proof.
  intro *. 
  expandall.  
  by typing Meq.
Qed.


