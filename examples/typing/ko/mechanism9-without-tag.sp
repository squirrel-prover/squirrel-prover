(** 
#Mechanism 9 without tag 
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb : nonce

    B -> A : Nb
    A -> S : Na, Nb, B
    S -> A : {Na, K, B}_Kas, {2, Nb, K, A}_Kbs
    A -> B : {Nb, K, A}_Kbs
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
lemma[any] cst_idD_id : forall i j, idD i <> id j.
Proof.
  intro i j H1.
  have H2 := cst_id_idD j i.
  smt.
Qed.
hint rewrite cst_idD_id.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Low * (High * Cst id)
                                  + Low * (High * Cst id)
                                  + Low * (Low * Cst idD)
                                  + Low * (Low * Cst idD)].

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
  IH1 : in(c,x); out(c, <Na(i,j,k), <x, id(j)>>);
  IH2:  in(c,y);  
       if  dec(fst(y),Ks(i)) <> fail 
        && fst(dec(fst(y),Ks(i))) = Na(i,j,k)
        && snd(snd(dec(fst(y),Ks(i)))) = id(j)
       then out(c, snd(y)).

process InitD(i,j,k:index)=
  ID1 : in(c,x); out(c, <NDa(i,j,k), <x, idD(j)>>);
  ID2:  in(c,y);  
       if  dec(fst(y),Ks(i)) <> fail 
        && fst(dec(fst(y),Ks(i))) = NDa(i,j,k)
        && snd(snd(dec(fst(y),Ks(i)))) = idD(j)
       then out(c, snd(y)).

process ServerHH(i,j,k:index)=
  SHH : in(c, x);
  if  snd(snd(x)) = id(j) 
  then out(c, <enc(<fst(x), <K(i,j,k),id(j)>>, Rsa(i,j,k),Ks(i)),
               enc(<fst(snd(x)), <K(i,j,k),id(i)>>,Rsb(i,j,k),Ks(j))>).

process ServerHD(i,j,k:index)=
  SHD : in(c, x);
  if  snd(snd(x)) = idD(j) 
  then out(c, <enc(<fst(x), <KHD(i,j,k),idD(j)>>, RHDsa(i,j,k),Ks(i)),
               enc(<fst(snd(x)), <KHD(i,j,k),id(i)>>,RHDsb(i,j,k),KDs(j))>).

process ServerDH(i,j,k:index)=
  SDH : in(c, x);
  if  snd(snd(x)) = id(j) 
  then out(c, <enc(<fst(x), <KDH(i,j,k),id(j)>>, RDHsa(i,j,k),KDs(i)),
               enc(<fst(snd(x)), <KDH(i,j,k),idD(i)>>,RDHsb(i,j,k),Ks(j))>).

process RespH(i,j,k:index)=
  RH1 : out(c, Nb(i,j,k));
  RH2:  in(c,y); 
       if   dec(y,Ks(j)) <> fail 
         && fst(dec(y,Ks(j))) = Nb(i,j,k)
         && snd(snd(dec(y,Ks(j)))) = id(i)
       then out(c,empty).

process RespD(i,j,k:index)=
  RD1 : out(c, NDb(i,j,k));
  RD2:  in(c,y); 
       if   dec(y,Ks(j)) <> fail 
         && fst(dec(y,Ks(j))) = NDb(i,j,k)
         && snd(snd(dec(y,Ks(j)))) = idD(i)
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
   if cond@IH2(i,j,k) then fst(snd(snd(dec(fst(input@IH2(i,j,k)),Ks(i))))) else Kfresh.
Proof.
  intro *. 
  expand cond. 
  checkfail typing Meq exn Failure.
Abort.

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
   if cond@RH2(i,j,k) then fst(snd(snd(dec(input@RH2(i,j,k), Ks(j))))) else Kfresh.
Proof.
  intro *. expand cond. 
  checkfail typing Meq exn Failure.
Abort.
