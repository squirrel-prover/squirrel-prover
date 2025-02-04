(** 
#Mechanism 13 - ISO 11770
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb : nonce
    1, 2, 3 : tag

    B -> A : Nb
    A -> S : {1, Na, Nb, B, K}_Kas
    S -> A : {2, Na, Nb, B}_Kas,  {3, Nb, K, A}_Kbs
    A -> B : {3, Nb, K, A}_Kbs
**)

set securityTypes = true.

include Logic.

channel c.

senc enc,dec.

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

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Cst tag1 * (Low * (Low * (Cst id * High)))
                                  + Cst tag2 * Low
                                  + Cst tag3 * (Low * (High * Cst id))].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.
name Na: index * index * index -> message, Low.
name Nb: index * index * index -> message, Low.
name Kfresh: message, High.

(* Randoms used in encryption *)
name Ra : index * index * index -> message, Rand.

name Rsa : index * index * index -> message, Rand.
name Rsb : index * index * index -> message, Rand.

process Init(i,j,k:index)=
  I1: in(c,x); out(c, enc(<tag1, <Na(i,j,k), <x, <id(j), K(i,j,k)>>>>,Ra(i,j,k),Ks(i)));
  I2: in(c,y);
      let mI = dec(fst(y),Ks(i)) in
      if mI <> fail 
      && fst(mI) = tag2
      && fst(snd(mI)) = Na(i,j,k)
      && fst(snd(snd(mI))) = x
      && snd(snd(snd(mI))) = id(j)
      then out(c, snd(y)).

process Server(i,j,k:index)=
  S: in(c, x);
     let mS = dec(x,Ks(i)) in
     let kS = snd(snd(snd(snd(mS)))) in
     if mS <> fail
     && fst(mS) = tag1
     && fst(snd(snd(snd(mS)))) = id(j)
     then out(c, <enc(<tag2,<fst(snd(mS)),<fst(snd(snd(mS))),id(j)>>>,Rsa(i,j,k),Ks(i)),
                  enc(<tag3,<fst(snd(snd(mS))), <snd(snd(snd(snd(mS)))),id(i)>>>, Rsb(i,j,k),Ks(j))>).

process Resp(i,j,k:index)=
  R1: out(c, Nb(i,j,k));
  R2: in(c,y); 
      let mR = dec(y,Ks(j)) in
      let kR = fst(snd(snd(mR))) in
      if mR <> fail 
      && fst(mR) = tag3
      && fst(snd(mR)) = Nb(i,j,k)
      && snd(snd(snd(mR))) = id(i)
      then out(c,empty).

system ( !_i !_j !_k ( Init(i,j,k) | Server(i,j,k) | Resp(i,j,k) )).

(* secrecy from the point of view of the initiator *)
 lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) =>  att(frame@tau) <> K(i,j,k).
Proof.
  intro *. 
  typing Meq. 
Qed.

(* secrecy from the point of view of the server *)
lemma key_secrecy_server: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) =>  tau >= S(i,j,k) => 
   att(frame@tau) <> 
   if cond@S(i,j,k) then kS i j k@S(i,j,k) else Kfresh.
Proof.
  intro *. 
  expandall.
  by typing Meq.
Qed.

(* secrecy from the point of view of the responder *)
lemma key_secrecy_resp : forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= R2(i,j,k) => 
   att(frame@tau) <> 
   if cond@R2(i,j,k) then kR i j k@R2(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall. 
  by typing Meq.
Qed.

