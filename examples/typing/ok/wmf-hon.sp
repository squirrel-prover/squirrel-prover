(** 
#Wide Mouthed Frog:
    A, S : principal
    Kas, Kbs, Kab : symkey

    A -> S : A, {B, K}Kas
    S -> B : {A, K}Kbs
**)

set securityTypes = true.

include Logic.

channel c.

senc enc,dec.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message, SK[enc, Cst id * High].

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message, High.
name Kfresh: message, High.

(* Randoms used in encryption *)
name Ra : index * index * index -> message, Rand.
name Rs : index * index * index -> message, Rand.


process Init(i,j,k:index)=
  I : out(c, <id(i), enc(<id(j), K(i,j,k)>, Ra(i,j,k), Ks(i))>).

process Server(i,j,k:index)=
  S: in(c, x);
     let mS = dec(snd(x), Ks(i)) in
     let kS = snd(mS) in
     if fst(x) = id(i) 
     && mS <> fail 
     && fst(mS) = id(j) 
     then out(c, enc(<id(i), snd(mS)>, Rs(i,j,k), Ks(j))).

process Resp(i,j,k:index)=
  R: in(c, x);
     let mR = dec(x, Ks(j)) in
     let kR = snd(mR) in
     if mR <> fail 
     && fst(mR) = id(i) 
     then out(c,empty).

system ( !_i !_j !_k (Init(i,j,k) | Server(i,j,k) | Resp(i,j,k))).

(* secrecy from the point of view of the initiator *)
lemma key_secrecy_init: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => att(frame@tau) <> K(i,j,k).
Proof.
  intro *.
  typing Meq.
Qed.

(* secrecy from the point of view of the server *)
lemma key_secrecy_server: forall (tau:timestamp), forall (i,j,k:index),
   happens(tau) => tau >= S(i,j,k) => 
   att(frame@tau) <> 
   if cond@S(i,j,k) then kS i j k@S(i,j,k) else Kfresh.
Proof.
  intro *.
  expandall. 
  by typing Meq.
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
