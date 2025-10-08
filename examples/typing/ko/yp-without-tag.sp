(** 
#Yahalom without tag 
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb : nonce

    A -> B : A, Na
    B -> S : B, Nb, {A, Na}_Kbs
    S -> A : Nb, {B, K, Na}_Kas, {A, B K, Nb}_Kbs
    A -> B : {A, B, K, Nb}_Kbs
**)

set securityTypes = true.

include Logic.

channel c.

senc enc,dec.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.
(* idD(i) is the identifier of dishonest agent i *)
abstract idD : index -> message.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Low
                                  + Cst id * (High * Low)
                                  + Cst id * (Low * (High * Low))
                                  + Cst idD *  Low
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
       if  dec(fst(snd(x)),Ks(i)) <> fail 
        && fst(dec(fst(snd(x)),Ks(i))) = id(j)
        && snd(snd(dec(fst(snd(x)),Ks(i)))) = Na(i,j,k)
       then out(c, snd(snd(x))).

process InitD(i,j,k:index)=
  ID1 : out(c, <id(i),NDa(i,j,k)>);
  ID2:  in(c,x);  
       if  dec(fst(snd(x)),Ks(i)) <> fail 
        && fst(dec(fst(snd(x)),Ks(i))) = idD(j)
        && snd(snd(dec(fst(snd(x)),Ks(i)))) = NDa(i,j,k)
       then out(c, snd(snd(x))).

process ServerHH(i,j,k:index)=
  SHH : in(c, x);
  if  fst(x) = id(j) 
   && dec(snd(snd(x)),Ks(j))  <> fail
   && fst(dec(snd(snd(x)),Ks(j))) = id(i)
  then out(c, <fst(snd(x)), 
              <enc(<id(j),<K(i,j,k),snd(snd(dec(snd(snd(x)),Ks(j))))>>, Rsa(i,j,k),Ks(i)),
               enc(<id(i),<id(j),<K(i,j,k),fst(snd(x))>>>,Rsb(i,j,k),Ks(j))>>).


process ServerHD(i,j,k:index)=
  SHD : in(c, x);
  if  fst(x) = idD(j) 
   && dec(snd(snd(x)),KDs(j))  <> fail
   && fst(dec(snd(snd(x)),KDs(j))) = id(i)
  then out(c, <fst(snd(x)), 
              <enc(<idD(j),<KHD(i,j,k),snd(snd(dec(snd(snd(x)),KDs(j))))>>, RHDsa(i,j,k),Ks(i)),
               enc(<id(i),<idD(j),<KHD(i,j,k),fst(snd(x))>>>,RHDsb(i,j,k),KDs(j))>>).


process ServerDH(i,j,k:index)=
  SDH : in(c, x);
  if  fst(x) = id(j) 
   && dec(snd(snd(x)),Ks(j))  <> fail
   && fst(dec(snd(snd(x)),Ks(j))) = idD(i)
  then out(c, <fst(snd(x)), 
              <enc(<id(j),<KDH(i,j,k),snd(snd(dec(snd(snd(x)),Ks(j))))>>, RDHsa(i,j,k),KDs(i)),
               enc(<idD(i),<id(j),<KDH(i,j,k),fst(snd(x))>>>,RDHsb(i,j,k),Ks(j))>>).

process RespH(i,j,k:index)=
  RH1 : in(c, x);
  if  fst(x) = id(i)
  then out(c,<id(j), <Nb(i,j,k), enc(<id(i), snd(x)>, Rb(i,j,k),Ks(j))>>);
  RH2:  in(c,y); 
       if   dec(y,Ks(j)) <> fail 
         && fst(dec(y,Ks(j))) = id(i)
         && fst(snd(dec(y,Ks(j)))) = id(j)
         && snd(snd(dec(y,Ks(j)))) = Nb(i,j,k)
       then out(c,empty).

process RespD(i,j,k:index)=
  RD1 : in(c, x);
  if  fst(x) = idD(i)
  then out(c,<id(j), <NDb(i,j,k), enc(<idD(i), snd(x)>, RDb(i,j,k),Ks(j))>>);
  RD2:  in(c,y); 
       if   dec(y,Ks(j)) <> fail 
         && fst(dec(y,Ks(j))) = id(i)
         && fst(snd(dec(y,Ks(j)))) = id(j)
         && snd(snd(dec(y,Ks(j)))) = NDb(i,j,k)
       then out(c,empty).

system ( !_i !_j !_k (InitH(i,j,k) | ServerHH(i,j,k) | RespH(i,j,k)  | 
                      InitD(i,j,k) | ServerHD(i,j,k) | 
                                     ServerDH(i,j,k)| RespD(i,j,k) 
)).



(* secrecy from the point of view of the initiator *)
 lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= IH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@IH2(i,j,k) then fst(snd(snd(dec(fst(snd(input@IH2(i,j,k))),Ks(i))))) else Kfresh.
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
  checkfail typing Meq exn Failure.
Abort.

(* secrecy from the point of view of the responder *)
lemma key_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= RH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@RH2(i,j,k) then fst(snd(snd(snd(dec(input@RH2(i,j,k), Ks(j)))))) else Kfresh.
Proof.
  intro *.
  expand cond. 
  checkfail typing Meq exn Failure.
Abort.
