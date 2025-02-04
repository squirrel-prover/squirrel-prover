(** 
#Yahalom without tag 
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb : nonce

    A -> B : A, Na
    B -> S : B, {A, Na, Nb}_Kbs
    S -> A : {B, K, Na, Nb}_Kas, {3, A, K}_Kbs
    A -> B : {A, K}_Kbs
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

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Low
                                  + Cst id * (High * Low)
                                  + Cst id * High
                                  + Cst idD * (Low * Low)
                                  + Cst idD * Low].

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
  IH1 : out(c, <id(i),Na(i,j,k)>);
  IH2:  in(c,x);  
       if  dec(fst(x),Ks(i)) <> fail 
        && fst(dec(fst(x),Ks(i))) = id(j)
        && fst(snd(snd(dec(fst(x),Ks(i))))) = Na(i,j,k)
       then out(c, snd(x)).

process InitD(i,j,k:index)=
  ID1 : out(c, <id(i),Na(i,j,k)>);
  ID2:  in(c,x);  
       if  dec(fst(x),Ks(i)) <> fail 
        && fst(dec(fst(x),Ks(i))) = id(j)
        && fst(snd(snd(dec(fst(x),Ks(i))))) = NDa(i,j,k)
       then out(c, snd(x)).

process ServerHH(i,j,k:index)=
  SHH : in(c, x);
  if  fst(x) = id(j) 
   && dec(snd(x),Ks(j))  <> fail
   && fst(dec(snd(x),Ks(j))) = id(i)
  then out(c, <enc(<id(j),<K(i,j,k),<fst(snd(dec(snd(x),Ks(j)))), 
                                           snd(snd(dec(snd(x),Ks(j))))>>>,Rsa(i,j,k),Ks(i)),
               enc(<id(i),K(i,j,k)>,Rsb(i,j,k),Ks(j))>).

process ServerHD(i,j,k:index)=
  SHD : in(c, x);
  if  fst(x) = idD(j) 
   && dec(snd(x),KDs(j))  <> fail
   && fst(dec(snd(x),KDs(j))) = id(i)
  then out(c, <enc(<idD(j),<KHD(i,j,k),<fst(snd(dec(snd(x),KDs(j)))), 
                                           snd(snd(dec(snd(x),KDs(j))))>>>,RHDsa(i,j,k),Ks(i)),
               enc(<id(i),KHD(i,j,k)>,RHDsb(i,j,k),KDs(j))>).

process ServerDH(i,j,k:index)=
  SDH : in(c, x);
  if  fst(x) = id(j) 
   && dec(snd(x),Ks(j))  <> fail
   && fst(dec(snd(x),Ks(j))) = idD(i)
  then out(c, <enc(<id(j),<KDH(i,j,k),<fst(snd(snd(dec(snd(x),Ks(j))))), 
                                           snd(snd(dec(snd(x),Ks(j))))>>>,RDHsa(i,j,k),KDs(i)),
               enc(<idD(i),KDH(i,j,k)>,RDHsb(i,j,k),Ks(j))>).


process RespH(i,j,k:index)=
  RH1 : in(c, x);
  if  fst(x) = id(i)
  then out(c,<id(j), enc(<id(i), <snd(x),Nb(i,j,k)>>,Rb(i,j,k),Ks(j))>);
  RH2:  in(c,y); 
       if   dec(y,Ks(j)) <> fail 
         && fst(dec(y,Ks(j))) = id(i)
       then out(c,empty).


process RespD(i,j,k:index)=
  RD1 : in(c, x);
  if  fst(x) = idD(i)
  then out(c,<id(j), enc(<idD(i), <snd(x),NDb(i,j,k)>>,RDb(i,j,k),Ks(j))>);
  RD2:  in(c,y); 
       if   dec(y,Ks(j)) <> fail 
         && fst(dec(y,Ks(j))) = idD(i)
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
   if cond@RH2(i,j,k) then snd(snd(dec(input@RH2(i,j,k), Ks(j)))) else Kfresh.
Proof.
  intro *.
  expand cond. 
  checkfail typing Meq exn Failure.
Abort.

