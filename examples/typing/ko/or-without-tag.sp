(** 
#Otways-Rees without tag 
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb, M : nonce
    A -> B : M, A, B, {Na, M, A, B}_Kas
    B -> S : A, B, {Na, M, A, B}_Kas, {Nb, M, A, B}_Kbs
    S -> B : {Na, K}_Kas, {Nb, K}_Kbs
    B -> A : {Na, K}Kas
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
name Ks : index -> message, SK[enc, High * (Low * (Cst id * Cst id))
                                  + Low * (Low * (Cst id * Cst idD))
                                  + Low * (Low * (Cst idD * Cst id))
                                  + High * High
                                  + Low * Low].

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
  IH1 : out(c, <M(i,j,k), <id(i),<id(j),
              enc(<Na(i,j,k), <M(i,j,k), <id(i),id(j)>>>, Ra(i,j,k),Ks(i))>>>);
  IH2:  in(c,x);  
       if  dec(x,Ks(i)) <> fail 
        && fst(dec(x,Ks(i))) = Na(i,j,k)
       then out(c, empty).

process InitD(i,j,k:index)=
  ID1 : out(c, <MD(i,j,k), <id(i),<idD(j),
              enc(<NDa(i,j,k), <MD(i,j,k), <id(i),idD(j)>>>, RDa(i,j,k),Ks(i))>>>);
  ID2:  in(c,x);  
       if  dec(x,Ks(i)) <> fail 
        && fst(dec(x,Ks(i))) = NDa(i,j,k)
       then out(c, empty).

process ServerHH(i,j,k:index)=
  SHH : in(c, x);
  if  fst(x) = id(i) && fst(snd(x)) = id(j)
   && dec(fst(snd(snd(x))),Ks(i))  <> fail
   && dec(snd(snd(snd(x))),Ks(j)) <> fail
   && fst(snd(snd(dec(fst(snd(snd(x))),Ks(i))))) = id(i)
   && snd(snd(snd(dec(fst(snd(snd(x))),Ks(i))))) = id(j)
   && fst(snd(snd(dec(snd(snd(snd(x))),Ks(j))))) = id(i)
   && snd(snd(snd(dec(snd(snd(snd(x))),Ks(j))))) = id(j) 
   && fst(snd(dec(fst(snd(snd(x))),Ks(i)))) = fst(snd(dec(snd(snd(snd(x))),Ks(j))))
  then out(c, <enc(<fst(dec(fst(snd(snd(x))),Ks(i))), K(i,j,k)>, Rsa(i,j,k), Ks(i)),
               enc(<fst(dec(snd(snd(snd(x))),Ks(j))), K(i,j,k)>, Rsb(i,j,k), Ks(j))>).

process ServerHD(i,j,k:index)=
  SHD : in(c, x);
  if  fst(x) = id(i) && fst(snd(x)) = idD(j)
   && dec(fst(snd(snd(x))),Ks(i))  <> fail
   && dec(snd(snd(snd(x))),KDs(j)) <> fail
   && fst(snd(snd(dec(fst(snd(snd(x))),Ks(i))))) = id(i)
   && snd(snd(snd(dec(fst(snd(snd(x))),Ks(i))))) = idD(j)
   && fst(snd(snd(dec(snd(snd(snd(x))),KDs(j))))) = id(i)
   && snd(snd(snd(dec(snd(snd(snd(x))),KDs(j))))) = idD(j) 
   && fst(snd(dec(fst(snd(snd(x))),Ks(i)))) = fst(snd(dec(snd(snd(snd(x))),KDs(j))))
 then out(c, <enc(<fst(dec(fst(snd(snd(x))),Ks(i))), KHD(i,j,k)>, RHDsa(i,j,k), Ks(i)),
               enc(<fst(dec(snd(snd(snd(x))),KDs(j))), KHD(i,j,k)>, RHDsb(i,j,k), KDs(j))>).

process ServerDH(i,j,k:index)=
  SDH : in(c, x);
  if  fst(x) = idD(i) && fst(snd(x)) = id(j)
   && dec(fst(snd(snd(x))),KDs(i))  <> fail
   && dec(snd(snd(snd(x))),Ks(j)) <> fail
   && fst(snd(snd(dec(fst(snd(snd(x))),KDs(i))))) = idD(i)
   && snd(snd(snd(dec(fst(snd(snd(x))),KDs(i))))) = id(j)
   && fst(snd(snd(dec(snd(snd(snd(x))),Ks(j))))) = idD(i)
   && snd(snd(snd(dec(snd(snd(snd(x))),Ks(j))))) = id(j) 
   && fst(snd(dec(fst(snd(snd(x))),KDs(i)))) = fst(snd(dec(snd(snd(snd(x))),Ks(j))))
  then out(c, <enc(<fst(dec(fst(snd(snd(x))),KDs(i))), KDH(i,j,k)>, RDHsa(i,j,k), KDs(i)),
               enc(<fst(dec(snd(snd(snd(x))),Ks(j))), KDH(i,j,k)>, RDHsb(i,j,k), Ks(j))>).

process RespH(i,j,k:index)=
  RH1 : in(c, x);
  if  fst(snd(snd(x))) = id(j)
  then out(c,<id(i), <id(j), <snd(snd(snd(x))), enc(<Nb(i,j,k), <fst(x), <id(i),id(j)>>>, Rb(i,j,k),Ks(j))>>>);
  RH2:  in(c,y); 
       if   dec(snd(y),Ks(j)) <> fail 
         && fst(dec(snd(y),Ks(j))) = Nb(i,j,k)
       then out(c,fst(y)).

process RespD(i,j,k:index)=
  RD1 : in(c, x);
  if  fst(snd(snd(x))) = id(j)
  then out(c,<idD(i), <id(j), <snd(snd(snd(x))), enc(<NDb(i,j,k), <fst(x), <idD(i),id(j)>>>, RDb(i,j,k),Ks(j))>>>);
  RD2:  in(c,y); 
       if   dec(snd(y),Ks(j)) <> fail 
         && fst(dec(snd(y),Ks(j))) = NDb(i,j,k)
       then out(c,fst(y)).

system ( !_i !_j !_k (InitH(i,j,k) | ServerHH(i,j,k) | RespH(i,j,k)  | 
                      InitD(i,j,k) | ServerHD(i,j,k) | 
                                     ServerDH(i,j,k) | RespD(i,j,k)
)).


(* secrecy from the point of view of the initiator *)
lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= IH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@IH2(i,j,k) then snd(snd(dec(input@IH2(i,j,k),Ks(i)))) else Kfresh.
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
   if cond@RH2(i,j,k) then snd(snd(dec(snd(input@RH2(i,j,k)), Ks(j)))) else Kfresh.
Proof.
  intro *.
  expand cond. 
  checkfail typing Meq exn Failure.
Abort.

