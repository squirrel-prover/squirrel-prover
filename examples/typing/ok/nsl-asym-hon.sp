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

name Na: index * index  * index -> message, High.
name Nb: index * index * index -> message, High.
name Kfresh: message, High.

(* Randoms used in encryption *)
name Ra1 : index * index * index -> message, Rand.
name Rb : index * index * index -> message, Rand.
name Ra2 : index * index * index -> message, Rand.

process Init(i,j,k:index)=
  I1: out(c, enc(<tag1, <Na(i,j,k),id(i)>>,Ra1(i,j,k),pk(sKey(j))));
  I2: in(c,x);
      let m = dec(x,sKey(i)) in
      let t = fst(m) in
      let na = fst(snd(m)) in
      let nb = fst(snd(snd(m))) in
      let ident = snd(snd(snd(m))) in
      if m <> fail 
      && t = tag2
      && na = Na(i,j,k)
      && ident = id(j)
      then out(c, enc(<tag3, nb>, Ra2(i,j,k), pk(sKey(j)))). 

process Resp(i,j,k:index)=
  R1: in(c, x);
      let m1 = dec(x,sKey(j)) in
      let t1 = fst(m1) in
      let na = fst(snd(m1)) in
      let ident1 = snd(snd(m1)) in
      if dec(x, sKey(j)) <> fail 
      && t1 = tag1
      && ident1 = id(i) 
      then out(c,enc(<tag2, <na, <Nb(i,j,k), id(j)>>>, Rb(i,j,k), pk(sKey(i))));
  R2: in(c,y);
      let m2 = dec(y,sKey(j)) in
      let t2 = fst(m2) in
      let nb = snd(m2) in
      if m2 <> fail
      && t2 = tag3
      && nb = Nb(i,j,k) 
      then out(c,empty). 

system ( !_i !_j !_k out(c,pk(sKey(i))); out(c,pk(sKey(j)));(  Init(i,j,k)  | Resp(i,j,k) )).

(* secrecy from the point of view of the responder *)
lemma Nb_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => att(frame@tau) <> Nb(i,j,k).
Proof.
  intro *.
  typing Meq.
Qed.


(* secrecy from the point of view of the initiator *)
lemma Nb_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= I2(i,j,k) => 
   att(frame@tau) <> 
   if cond@I2(i,j,k) then nb i j k@I2(i,j,k) else Kfresh.
Proof.
  intro *. 
  expandall.
  by typing Meq.
Qed.


