(** 
#Otways-Rees 
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb, M : nonce
    req, rep : tag
    A -> B : M, A, B, {req, Na, M, A, B}_Kas
    B -> S : A, B, {req, Na, M, A, B}_Kas, {req, Nb, M, A, B}_Kbs
    S -> B : {rep, Na, K}_Kas, {rep, Nb, K}_Kbs
    B -> A : {rep, Na, K}Kas
**)

set securityTypes = true.

include Logic.

channel c.

senc enc,dec.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.
(* tag *)
abstract req: message. 
abstract rep: message. 
axiom[any] cst_diff1 : rep <> req.
hint rewrite cst_diff1.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Cst req * (High * (Low * (Cst id * Cst id))) + Cst rep * (High * High)].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.
name Na: index * index * index -> message, High.
name Nb: index * index * index -> message, High.
name M: index * index * index -> message, Low.
name Kfresh: message, High.

(* Randoms used in encryption *)
name Ra : index * index * index -> message, Rand.
name Rb : index * index * index -> message, Rand.
name Rsa : index * index * index -> message, Rand.
name Rsb : index * index * index -> message, Rand.

process Init(i,j,k:index)=
  I1: out(c, <M(i,j,k), <id(i),<id(j),
              enc(<req, <Na(i,j,k), <M(i,j,k), <id(i),id(j)>>>>, Ra(i,j,k),Ks(i))>>>);
  I2: in(c,x);  
      let mI = dec(x,Ks(i)) in
      let kI = snd(snd(mI)) in
      if mI <> fail  && fst(mI) = rep && fst(snd(mI)) = Na(i,j,k)
      then out(c, empty).

process Server(i,j,k:index)=
  S: in(c, x);
     let mSA = dec(fst(snd(snd(x))),Ks(i)) in
     let mSB = dec(snd(snd(snd(x))),Ks(j)) in
     if fst(x) = id(i) && fst(snd(x)) = id(j) && mSA <> fail && mSB <> fail
     && fst(mSA) = req && fst(mSB) = req
     && snd(snd(snd(mSA))) = <id(i), id(j)> 
     && snd(snd(snd(mSB))) = <id(i), id(j)>
     && fst(snd(snd(mSA))) = fst(snd(snd(mSB))) 
     then out(c, <enc(<rep,<fst(snd(mSA)), K(i,j,k)>>, Rsa(i,j,k), Ks(i)),
                  enc(<rep,<fst(snd(mSB)), K(i,j,k)>>, Rsb(i,j,k), Ks(j))>).

process Resp(i,j,k:index)=
  R1: in(c, x);
      if fst(snd(snd(x))) = id(j)
      then out(c,<id(i), <id(j), <snd(snd(snd(x))), enc(<req, <Nb(i,j,k), <fst(x), <id(i),id(j)>>>>, Rb(i,j,k),Ks(j))>>>);
  R2: in(c,y); 
      let mR = dec(snd(y),Ks(j)) in
      let kR = snd(snd(mR)) in
      if mR <> fail && fst(mR) = rep && fst(snd(mR)) = Nb(i,j,k)
      then out(c,fst(y)).

system ( !_i !_j !_k ( Init(i,j,k) | Server(i,j,k) | Resp(i,j,k) )).

(* secrecy from the point of view of the initiator *)
 lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= I2(i,j,k) => 
   att(frame@tau) <> 
   if cond@I2(i,j,k) then (kI i j k)@I2(i,j,k) else Kfresh.
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
   happens(tau) => tau >= R2(i,j,k) => 
   att(frame@tau) <> 
   if cond@R2(i,j,k) then (kR i j k)@R2(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall.
  by typing Meq.
Qed.

