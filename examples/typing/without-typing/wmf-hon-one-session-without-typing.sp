(** 
#Wide Mouthed Frog:
    A, S : principal
    Kas, Kbs, Kab : symkey

    A -> S : A, {B, K}Kas
    S -> B : {A, K}Kbs

Only 2 agents and one session.
Je supprime l'output du role R pour me simplifier la vie.
**)

include Basic.

channel c.


(* encryption function *)
senc enc,dec.

lemma [any] dec_enc (x,r,y:message) : dec(enc(x,r,y),y) = x.
Proof.
  congruence.
Qed.
hint rewrite dec_enc.


abstract idA : message.
abstract idB : message.

name KAs :  message.
name KBs :  message

name K : message.
name Kfresh: message.

(* Randoms used in encryption *)
name Ra :  message.
name Rs :  message.

axiom [any] distinct_id : idA <> idB.


(* a public value of the same length as K *)
abstract dummy : message.
axiom [any] dummy_len : len dummy = namelength_message.
hint rewrite dummy_len.

hint rewrite namelength_K.

(* axiom: pairing same-length messages yields same-length pairs *)
axiom [any] len_pair (x, y, x', y':message) :
  len x = len x' =>
  len y = len y' =>
  len (<x, y>) = len (<x', y'>).



process Init =
  I : out(c, <idA, enc(<idB, K>, Ra, KAs)>).

process Server =
  S : in(c, x);
  if 
    fst(x) = idA &&
    dec(snd(x), KAs) <> fail &&
    fst(dec(snd(x), KAs)) = idB
  then 
    out(c, enc(<idA, snd(dec(snd(x), KAs))>, Rs, KBs)).

process Resp =
  R : in(c, x).

system (Init | Server | Resp).


(* --------------------------------------------------------------- *)


lemma AccSsnd :
  happens(S) =>
  (cond@S <=> 
    (I < S && 
     fst(input@S) = idA && 
     snd(input@S) = snd(output@I))).
Proof.
  intro Hap.
  rewrite /cond.
  split.
  + intro [H1 H2 H3].
    by intctxt H2. 
  + intro [H1 H2 H3]. 
    rewrite H3 /output /=.
    intro Heq.
    apply (f_apply snd) in Heq; simpl.
    by fresh Heq.
Qed.


lemma AccS1snd :
  happens(S1) => 
  (cond@S1 <=> 
   not (I < S1 && 
        fst(input@S1) = idA && 
        snd(input@S1) =  snd(output@I))
  ).
Proof.
  intro Hap.
  rewrite /cond.
  split. 
  + intro Hcond [H1 H2 H3].
    rewrite H2 H3 /output /= in Hcond.
    apply (f_apply snd) in Hcond; simpl.  
    by fresh Hcond.
  + intro H [H1 H2 H3].
    by intctxt H2.
Qed.


global lemma StrongSecrecyServer :
Forall (t:timestamp[const]), 
  [happens(t)] -> 
  equiv(frame@t, diff(K,Kfresh)).
Proof.
  intro t Hap.
  enrich (enc(<idB, K>, Ra, KAs)).
  enrich (enc(<idA, K>, Rs, KBs)).
  induction t.
  (* init *)
  * cca1 0 => //. 
    rewrite (len_pair _ _ idA dummy) // in 0.
    cca1 1 => //.
    rewrite (len_pair _ _ idB dummy) // in 1.
    by fresh 3.
  
  (* I *)
  * rewrite /frame /exec /cond /output.
    by apply IH.  

 (* S *)
  * rewrite /frame /output /exec. 
    fa !<_,_>.
    assert (cond@S => snd (input@S) = snd (output@I)) as H.
    by rewrite AccSsnd.
    by rewrite H AccSsnd.
    
 (* S1 *)
  * rewrite /frame /output /exec.
    fa !<_,_>.  
    by rewrite AccS1snd.

 (* R *)
  * rewrite /frame /output /exec /cond.
    by fa !<_,_>. 
Qed.


lemma [set:default/left; equiv:default] SecrecyServer (t:timestamp[glob]) :
    happens(t) =>
    att(frame@t) <> K.
Proof.
  intro Hap.
  use (StrongSecrecyServer t) as H => //.
  rewrite equiv H.
  intro Heq.
  by fresh Heq.
Qed.
