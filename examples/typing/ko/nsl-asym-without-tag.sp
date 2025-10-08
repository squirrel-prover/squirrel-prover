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
axiom[any] cst_id_idD : forall i j, id i <> idD j.
hint rewrite cst_id_idD.

(* sKey(i) long-term private key of (honest) agent id(i) *)
name sKey : index -> message, AK[enc, (High * Cst id)
                                    + (Msg * (High * Cst id))
                                    + High
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
  IH1 : out(c, enc(<Na(i,j,k),id(i)>,Ra1(i,j,k),pk(sKey(j))));
  IH2:  in(c,x);  
       if  dec(x,sKey(i)) <> fail 
        && fst(dec(x,sKey(i))) = Na(i,j,k)
        && snd(snd(dec(x,sKey(i)))) = id(j)
       then out(c, enc(fst(dec(x,sKey(i))), Ra2(i,j,k), pk(sKey(j)))). 

process InitD(i,j,k:index)=
  ID1 : out(c, enc(<NDa(i,j,k),id(i)>,RDa1(i,j,k),pk(sKeyD(j))));
  ID2:  in(c,x);  
       if  dec(x,sKey(i)) <> fail 
        && fst(dec(x,sKey(i))) = NDa(i,j,k)
        && snd(snd(dec(x,sKey(i)))) = idD(j)
       then out(c, enc(fst(dec(x,sKey(i))), RDa2(i,j,k), pk(sKeyD(j)))). 

process RespH(i,j,k:index)=
  RH1 : in(c, x);
  if  dec(x, sKey(j)) <> fail 
   && snd(dec(x,sKey(j))) = id(i) 
  then out(c,enc(<fst(dec(x,sKey(j))), <Nb(i,j,k), id(j)>>, Rb(i,j,k), pk(sKey(i))));  
RH2 : in(c,y);
  if dec(y,sKey(j)) <> fail
  && dec(y,sKey(j)) = Nb(i,j,k) 
  then out(c,empty). 

process RespD(i,j,k:index)=
  RD1 : in(c, x);
  if  dec(x, sKey(j)) <> fail 
   && snd(dec(x,sKey(j))) = idD(i) 
  then out(c,enc(<fst(dec(x,sKey(j))), <NDb(i,j,k), id(j)>>, RDb(i,j,k), pk(sKeyD(i))));  
RD2 : in(c,y);
  if dec(y,sKey(j)) <> fail
  && dec(y,sKey(j)) = NDb(i,j,k) 
  then out(c,empty). 

system ( !_i !_j !_k out(c,pk(sKey(i))); out(c,pk(sKey(j)));(  InitD(i,j,k)  | RespD(i,j,k)  |  InitH(i,j,k)  | RespH(i,j,k)  )).

(* secrecy from the point of view of the responder *)
lemma Nb_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => att(frame@tau) <> Nb(i,j,k).
Proof.
  intro *.
  checkfail typing Meq exn Failure.
Abort.


(* secrecy from the point of view of the initiator *)
lemma Nb_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= IH2(i,j,k) => 
   att(frame@tau) <> 
   if cond@IH2(i,j,k) then fst(snd(snd(dec(input@IH2(i,j,k),sKey(i))))) else Kfresh.
Proof.
  intro *. 
  expand cond.
  checkfail typing Meq exn Failure.
Abort.


