(** 
#Wide Mouthed Frog:
    A, S : principal
    Kas, Kbs, Kab : symkey

    A -> S : A, {1, B, K}Kas
    S -> B : {2, A, K}Kbs
**)

channel c.

senc enc,dec.

abstract tag1: message.
abstract tag2: message.

axiom [any] tag_distinct: tag1 <> tag2.

(* id(i) identifier of (honest) agent i *)
abstract id : index -> message.

(* Ks(i) long-term key shared between id(i) and the server *)
name Ks : index -> message.

(* K(i,j,h) session key established by agent id(i) with agent id(j) at session k *)
name K : index * index * index -> message.
name Kfresh: message.

(* Randoms used in encryption *)
name Ra : index * index * index -> message.
name Rs : index * index * index -> message.

axiom [any] distinct_id(i,j:index) : id(i) = id(j) => i=j.

lemma [any] dec_enc (x,r,y:message) : dec(enc(x,r,y),y) = x.
Proof.
  congruence.
Qed.
hint rewrite dec_enc.

lemma [any] fst_pair (x,y:message) : fst(<x,y>) = x.
Proof.
  congruence.
Qed.
hint rewrite fst_pair.

lemma [any] snd_pair (x,y:message) : snd(<x,y>) = y.
Proof.
  congruence.
Qed.
hint rewrite fst_pair.


process Init(i,j,k:index)=
  I : out(c, <id(i), enc(<tag1, <id(j), K(i,j,k)>>, Ra(i,j,k), Ks(i))>).

process Server(i,j,k:index)=
  S : in(c, x);

  if  fst(x) =   id(i)   
  && dec(snd(x), Ks(i)) <> fail 
  && fst(dec(snd(x), Ks(i))) = tag1
   && fst(snd(dec(snd(x), Ks(i)))) = id(j) 
  then out(c, enc(<tag2, <id(i), snd(dec(snd(x), Ks(i)))>>, Rs(i,j,k), Ks(j))).

process Resp(i,j,k:index)=
  R : in(c, x);
  if  dec(x, Ks(j)) <> fail 
   && fst(dec(x,Ks(j))) = tag2
   && fst(snd(dec(x, Ks(j)))) = id(i) 
  then out(c,empty).

system ( !_i !_j !_k (Init(i,j,k) | Server(i,j,k) | Resp(i,j,k))).


lemma  AccSfst (i,j,k:index) : happens(S(i,j,k)) => cond@S(i,j,k) =>
 fst(input@S(i,j,k)) = id(i).
Proof.
intro Hap. intro Hcond. expand cond@S(i,j,k).  destruct Hcond as [H1 H2 H3].
auto. 
Qed.


lemma AccSsnd (i,j,k:index) : happens(S(i,j,k)) => cond@S(i,j,k) => (
(exists k':index,
 snd(input@S(i,j,k)) = enc(<tag1, <id(j),K(i,j,k')>>,Ra(i,j,k'),Ks(i)))).
Proof.
intro Hap. intro Hcond. expand cond@S(i,j,k).  destruct Hcond as [H1 H2 H3]. 
intctxt H2. intro [j0 k0 HH]. destruct HH as [HH1 HH2]. 
rewrite HH2 in H3. simpl. 
use distinct_id with j0,j => //. 
rewrite Ieq in *.

exists k0. 
auto.

intro [i0 k0 HH].
destruct HH as [HH1 HH2]. 
rewrite HH2 in H3.

simpl.
use tag_distinct.
auto.
Qed.


global lemma StrongSecrecyServer : Forall (t:timestamp[const]), Forall (i0,j0,k0:index[const]), 
[happens(t)] -> equiv(frame@t,
seq(i,j,k:index => enc(<tag1, <id j, K(i,j,k)>>, Ra(i,j,k), Ks i)),
seq(i,j,k:index => enc(<tag2, <id i, K(i,j,k)>>, Rs(i,j,k), Ks j)),

diff(K(i0,j0,k0),Kfresh)).
Proof.
intro t.
intro i0 j0 k0.
intro Hap.
induction t.
 (* init *)
  * expandall. admit 0. (* cca sur une sequence mais en fait cela ne sera pas possible d'appliquer cca puisque la clef apparait en claire dans l'item 2*) admit 0.  fresh 0 => //.
 (* I *)
  * expandall. apply IH.  
 (* S *)
  * rewrite /frame. fa !<_,_>. rewrite /exec. expand output@S(i,j,k).
use AccSsnd with i,j,k. (* rewrite H in 2. *)
(* Ne marche pas  et meme si cela marchait, je vais me retrouver dans l'item 2 avec un chiffrement de K(i,j,k') et l'utilisation d'un random Rs(i,j,k) -- sans garantie que k=k' et donc ma sequence  4 ne subsumera pas ce message *)
admit 2.  

(* en chantier *)

Qed.


(* Je me dis qu'il faudrait sans doute etablir un lemme de well-authentification qui dit que cond@S(i,j,k) est vraie ssi (il exists k' such that I(i,j,k') < S(i,j,k) && ... mais la encore je ne peux pas imposer que k=k' et je pense que cela va poser des soucis . *)
