(** 
#Wide Mouthed Frog:
    A, S : principal
    Kas, Kbs, Kab : symkey

    A -> S : A, {B, K}Kas
    S -> B : {A, K}Kbs
**)

set securityTypes = true.

include Logic.

channel c.

senc enc,dec.

(* id(i) identifier of honest agent i *)
abstract id : index -> message.
(* idD(i) is the identifier of dishonest agent i *)
abstract idD : index -> message.
axiom[any] cst_id_idD : forall i j, id i <> idD j <: Real.z.
hint rewrite cst_id_idD.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Cst id * High + Cst idD * Low].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.

(* KDs(i) long-term key shared between idD(i) and the server *)
name KDs : index -> message, Low.

(* KD(i,j,k) session key established by agent id(i) with dishonest agent idD(j) at session k *)
name KD : index * index * index -> message, Low.
name Kfresh : message, High.

(* Randoms used in encryptions *)
name Ra : index * index * index -> message, Rand.
name RDa : index * index * index -> message, Rand.
name Rs : index * index * index -> message, Rand.
name RHDs : index * index * index -> message, Low.
name RDHs : index * index * index -> message, Rand.

process InitH(i,j,k:index)=
  IH: out(c, <id(i), enc(<id(j), K(i,j,k)>, Ra(i,j,k), Ks(i))>).

process InitD(i,j,k:index)=
  ID: out(c, <id(i), enc(<idD(j), KD(i,j,k)>, RDa(i,j,k), Ks(i))>).

process ServerHH(i,j,k:index)=
  SHH: in(c, x);
       let mSHH = dec(snd(x), Ks(i)) in
       let kS = snd(mSHH) in
       if fst(x) = id(i) 
       && mSHH <> fail 
       && fst(mSHH) = id(j) 
       then out(c, enc(<id(i), snd(mSHH)>, Rs(i,j,k), Ks(j))).

process ServerHD (i,j,k:index)=
  SHD: in(c, x);
       let mSHD = dec(snd(x), Ks(i)) in
       if fst(x) = id(i) 
       && mSHD <> fail 
       && fst(mSHD) = idD(j) 
       then out(c, enc(<id(i), snd(mSHD)>, RHDs(i,j,k), KDs(j))).

process ServerDH (i,j,k:index)=
  SDH: in(c, x);
       let mSDH = dec(snd(x), KDs(i)) in
       if fst(x) = idD(i) 
       && mSDH <> fail 
       && fst(mSDH) = id(j) 
       then out(c, enc(<idD(i), snd(mSDH)>, RDHs(i,j,k), Ks(j))).

process RespH(i,j,k:index)=
  RH: in(c, x);
      let mRH = dec(x, Ks(j)) in
      let kR = snd(mRH) in
      if mRH <> fail 
      && fst(mRH) = id(i) 
      then out(c,empty).

process RespD (i,j,k:index)=
  RD: in(c, x);
      let mRD = dec(x, Ks(j)) in
      if mRD <> fail 
      && fst(mRD) = idD(i) 
      then out(c,empty).

system ( !_i !_j !_k (InitH(i,j,k) | ServerHH(i,j,k) | RespH(i,j,k) |
                      InitD(i,j,k) | ServerHD(i,j,k) |
                                     ServerDH(i,j,k) | RespD(i,j,k))).
Proof.
  auto.
Qed.

(* secrecy from the point of view of the initiator *)
lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => att(frame@tau) <> K(i,j,k).
Proof.
  intro *.
  typing Meq.
Qed.

(* secrecy from the point of view of the server *)
lemma key_secrecy_server: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= SHH(i,j,k) => 
   att(frame@tau) <> 
   if cond@SHH(i,j,k) then kS@SHH(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall. 
  by typing Meq.
Qed.

(* secrecy from the point of view of the responder *)
lemma key_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= RH(i,j,k) => 
   att(frame@tau) <> 
   if cond@RH(i,j,k) then kR@RH(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall. 
  by typing Meq.
Qed.

