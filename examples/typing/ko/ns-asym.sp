(** 
#Needham-Schroeder (asymmetric)
    A, B : principal
    Kas, Kbs, K : symkey
    Na : nonce

    A -> B : {1, Na, A}_pubB
    B -> A : {2, Na, Nb}_pubA
    A -> B : {3, Nb}_pubB
**)

set securityTypes = true.

include Logic.

channel c.

aenc enc,dec,pk.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.
(* tag *)
abstract tag1: message. 
abstract tag2: message. 
abstract tag3: message. 
axiom[any] cst12_diff : tag1 <> tag2.
axiom[any] cst13_diff : tag1 <> tag3.
axiom[any] cst23_diff : tag2 <> tag3.

(* sKey(i) long-term private key of (honest) agent id(i) *)
name sKey : index -> message, AK[enc, Cst tag1 * (High * Cst id)
                                    + Cst tag2 * (Msg * High)
                                    + Cst tag3 * High
                                    + Low].

name Na: index * index  * index -> message, High.
name Nb: index * index * index -> message, High.
name Kfresh: message, High.

(* Randoms used in encryption *)
name Ra1 : index * index * index -> message, Rand.
name Rb : index * index * index -> message, Rand.
name Ra2 : index * index * index -> message, Rand.

process Init(i,j,k:index)=
  I1 : out(c, enc(<tag1, <Na(i,j,k),id(i)>>,Ra1(i,j,k),pk(sKey(j))));
  I2:  in(c,x);  
       if  dec(x,sKey(i)) <> fail 
        && fst(dec(x,sKey(i))) = tag2
        && snd(dec(x,sKey(i))) = Na(i,j,k)
       then out(c, enc(<tag3, fst(snd(snd(dec(x,sKey(i)))))>, Ra2(i,j,k), pk(sKey(j)))). 

process Resp(i,j,k:index)=
  R1 : in(c, x);
  if  dec(x, sKey(j)) <> fail 
   && fst(dec(x,sKey(j))) = tag1
   && snd(snd(dec(x,sKey(j)))) = id(i) 
  then out(c,enc(<tag2, < fst(snd(dec(x,sKey(j)))), Nb(i,j,k)>>, Rb(i,j,k), pk(sKey(i))))
;  R2 : in(c,y);
  if dec(y,sKey(j)) <> fail
  && fst(dec(y,sKey(j))) = tag3
  && snd(dec(y,sKey(j))) = Nb(i,j,k) 
  then out(c,empty). 

system ( !_i !_j !_k out(c,pk(sKey(i))); out(c,pk(sKey(j)));(  Init(i,j,k)  | Resp(i,j,k) )).

(* secrecy from the point of view of the responder *)
lemma Nb_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => att(frame@tau) <> Nb(i,j,k).
Proof.
  intro *.
  checkfail typing Meq exn Failure.
Abort.


(* secrecy from the point of view of the initiator *)
lemma Nb_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= I2(i,j,k) => 
   att(frame@tau) <> 
   if cond@I2(i,j,k) then fst(snd(snd(dec(input@I2(i,j,k),sKey(i))))) else Kfresh.
Proof.
  intro *. 
  expand cond.
  checkfail typing Meq exn Failure.
Abort.

