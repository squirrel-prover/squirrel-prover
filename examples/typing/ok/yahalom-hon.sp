(** 
#Yahalom
    A, B, S : principal
    Kas, Kbs, K : symkey
    Na, Nb : nonce
    1, 2, 3 : tag

    A -> B : A, Na
    B -> S : B, {1, A, Na, Nb}_Kbs
    S -> A : {2, B, K, Na, Nb}_Kas, {3, A, K}_Kbs
    A -> B : {3, A, K}_Kbs
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
name Ks : index -> message, SK[enc, Cst tag1 * Low
                                  + Cst tag2 * (Cst id * (High * Low))
                                  + Cst tag3 * (Cst id * High)].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.
name Na: index * index * index -> message, Low.
name Nb: index * index * index -> message, Low.
name Kfresh: message, High.

(* Randoms used in encryption *)
name Rb : index * index * index -> message, Rand.
name Rsa : index * index * index -> message, Rand.
name Rsb : index * index * index -> message, Rand.


process Init(i,j,k:index)=
  I1: out(c, <id(i),Na(i,j,k)>);
  I2: in(c,x);
       let mI = dec(fst(x),Ks(i)) in
       let kI = fst(snd(snd(mI))) in
       if mI <> fail 
       && fst(mI) = tag2
       && fst(snd(mI)) = id(j)
       && fst(snd(snd(snd(mI)))) = Na(i,j,k)
       then out(c, snd(x)).

process Server(i,j,k:index)=
  S: in(c, x);
     let mS = dec(snd(x),Ks(j)) in
     if fst(x) = id(j) 
     && mS <> fail
     && fst(mS) = tag1
     && fst(snd(mS)) = id(i)
     then out(c, <enc(<tag2,<id(j),<K(i,j,k),<fst(snd(snd(mS))), 
                                              snd(snd(snd(mS)))>>>>,Rsa(i,j,k),Ks(i)),
                  enc(<tag3,<id(i),K(i,j,k)>>,Rsb(i,j,k),Ks(j))>).

process Resp(i,j,k:index)=
  R1: in(c, x);
      if fst(x) = id(i)
      then out(c,<id(j), enc(<tag1, <id(i), <snd(x),Nb(i,j,k)>>>,Rb(i,j,k),Ks(j))>);
  R2: in(c,y);
      let mR = dec(y,Ks(j)) in
      let kR = snd(snd(mR)) in
      if mR <> fail 
      && fst(mR) = tag3
      && fst(snd(mR)) = id(i)
      then out(c,empty).

system ( !_i !_j !_k ( Init(i,j,k) | Server(i,j,k) | Resp(i,j,k) )).

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
   happens(tau) => tau >= R2(i,j,k) => 
   att(frame@tau) <> 
   if cond@R2(i,j,k) then kR i j k@R2(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall. 
  by typing Meq.
Qed.

