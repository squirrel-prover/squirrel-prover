(** 
#Denning-Sacco 
    A, B, S : principal
    Kas, Kbs, K : symkey

    A -> S : A, B
    S -> A {B, K, {resp, K, A}_Kbs}_Kas
    A -> B : {resp, K, A}Kbs
**)

set securityTypes = true.

include Logic.

channel c.

senc enc,dec.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.
(* tag *)
abstract resp: message.
(* axioms for different constants *)
axiom[any] cst_resp_id : forall i, id i <> resp.
hint rewrite cst_resp_id.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Cst id * (High * Low) + Cst resp * (High * Cst id)].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.
name Kfresh: message, High.

(* Randoms used in encryption *)
name Ra : index * index * index -> message, Rand.
name Rb : index * index * index -> message, Rand.


process Init(i,j,k:index)=
  I1: out(c, <id(i),id(j)>);
  I2: in(c,x);
      let mI = dec(x,Ks(i)) in
      let kI = fst(snd(mI)) in
      if mI <> fail 
      && fst(mI) = id(j)
      then out(c, snd(snd(mI))). 

process Server(i,j,k:index)=
  S: in(c, x);
     if fst(x) = id(i) && snd(x) = id(j)
     then out(c, enc(<id(j), <K(i,j,k), 
                 enc(<resp, <K(i,j,k), id(i)>>, Rb(i,j,k), Ks(j))>>, 
                 Ra(i,j,k), Ks(i))).

process Resp(i,j,k:index)=
  R: in(c, x);
     let mR = dec(x, Ks(j)) in
     let kR = fst(snd(mR)) in
     if mR <> fail 
     && fst(mR) = resp
     && snd(snd(mR)) = id(i)
     then out(c,empty).

system ( !_i !_j !_k (Init(i,j,k) | Server(i,j,k) | Resp(i,j,k))).
Proof.
  auto.
Qed.

(* secrecy from the point of view of the initiator *)
lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= I2(i,j,k) => 
   att(frame@tau) <> 
   if cond@I2(i,j,k) then kI i j k@I2(i,j,k) else Kfresh.
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
   happens(tau) => tau >= R(i,j,k) => 
   att(frame@tau) <> 
   if cond@R(i,j,k) then kR i j k@R(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall. 
  by typing Meq.
Qed.

