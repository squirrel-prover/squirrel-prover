(** Needham-Schroeder-Lowe protocol.*)

(* The NSL protocol describes the interaction between two participants,
   Alice (`A`) and Bob (`B`),
   who want to exchange their respective secret random data `nA` and `nB`
   without them beeing revealed to an active attacker.

   Each participant has its own secret encryption key and the two
   associated public keys `pkA` and `pkB` are distributed prior to
   the exchange, which is as follows:

   A -> B: {nA,pkA}_pkB
   B -> A: {nA,nB,pkB}_pkA
   A -> B: {nB,nA}_pkB

   In this file we prove that a simple scenario of this protocol
   is indistinguishabile from a variant where encrypted messages
   are replaced by their length (in unary), relying on the
   IND-CCA2 crypto assumption. We explain how this is useful to
   prove the strong secrecy of the exchanged nonces `nA` and `nB`.

   We consider a single session of each participant. The initiator
   `A` uses a public key that is chosen by the attacker, allowing
   man in the middle attacks.
   We assume a tagging mechanism to distinguish the first and last
   messages from `A`. *)

include Basic.

(* ------------------------------------------------------------------------ *)

(** Constructors and destructors for contents of the three messages.
    This amounts to minimal assumptions on how messages are formatted,
    but we make further assumptions about lengths and tags below. *)

abstract make1 : message * message -> message.
abstract get1_na : message -> message.
abstract get1_id : message -> message.
axiom [any] get1_na  (x,y:_) : get1_na(make1(x,y)) = x.

abstract make2 : message * message * message -> message.
abstract get2_na : message -> message.
abstract get2_nb : message -> message.
abstract get2_id : message -> message.
axiom [any] get2_na (x,y,z:_) : get2_na(make2(x,y,z)) = x.
axiom [any] get2_nb (x,y,z:_) : get2_nb(make2(x,y,z)) = y.
axiom [any] get2_id (x,y,z:_) : get2_id(make2(x,y,z)) = z.

abstract make3 : message * message -> message.
abstract get3_na : message -> message.
abstract get3_nb : message -> message.
axiom [any] get3_na (x,y:_) : get3_na(make3(x,y)) = x.
axiom [any] get3_nb (x,y:_) : get3_nb(make3(x,y)) = y.

(* ------------------------------------------------------------------------ *)

(** Asymmetric encryption and CCA2 game. *)

(* We rely on encryption and decryption functions such that,
   for any plaintext `m`, encryption key `k` and encryption randomness `r`,
   `dec (enc m k r) k = m`.

   We assume that encryption is secure against chosen-ciphertext
   attacks in the sense of the IND-CCA2 game.
   The game expresses the indistinguishability between
   two encrypted messages of same length.
   The adversary is given access to a challenge oracle `encrypt`
   that takes two inputs `m0`,`m1` and (provided they have the same length)
   returns:
   - in the left-game the encryption of `m0` and
   - in the right-game the encryption of `m1`.
   Moreover the adversary can also use a decryption oracle
   on any message other than the ones outputted by the `encrypt`
   oracle. *)

abstract pub : message -> message.
abstract dec : message*message -> message.
abstract enc : message*message*message -> message.

game CCA2 = {
  rnd key : message;
  var log = empty_set;
  oracle pk = {
    return (pub key)
  }
  oracle encrypt (m0,m1 : message) = {
    rnd r: message;
    var c = enc(diff(m0,m1),r,pub key);
    log := add c log ;
    return if zeroes m0 = zeroes m1 then c else empty
  }
  oracle decrypt (c : message) = {
    return if not (mem c log) then dec(c,key)
  }
}.

(* ------------------------------------------------------------------------ *)

(** Protocol description.
    We consider only one session of each role. *)

name ska : message.
name skb : message.

name na  : message.
name nb  : message.
name nb' : message.
name na' : message.
name r1  : message.
name r1' : message.
name r2  : message.
name r2' : message.
name r3  : message.
name r3' : message.

(* Introduce three constants that are assumed to have the same
   lengths, respectively, as the three messages.
   We also assume that len1 passes the tag verification associated
   to the first message, but that len3 and make3 results do not. *)
abstract len1 : message.
abstract len2 : message.
abstract len3 : message.

axiom [any] len1 : zeroes len1 = zeroes(make1(na,pub(ska))).
axiom [any] len2 : zeroes len2 = zeroes(make2(na,nb,pub(skb))).
axiom [any] len3 : zeroes len3 = zeroes(make3(nb,na)).

abstract check_tag : message -> bool.
axiom [any] check_tag_msg1 (x,y:message) : check_tag (make1(x,y)).
axiom [any] check_tag_msg3 (x,y:message) : not (check_tag (make3(x,y))).
axiom [any] check_tag_len1 : check_tag len1.
axiom [any] check_tag_len3 : not (check_tag len3).

channel c.

(* We define our main bi-system:
   - NSL/left is the real protocol;
   - NSL/right is the idealized protocol where the contents of encryptions
     are changed by zeroes.
   Note that NSL/left already "anticipates" the idealization by incorporating
   special cases in its logic (e.g. Bob outputs msg2 when msg1 is received)
   but this is obviously equivalent to the original specification (modulo
   axioms on tag verifications). *)

process Alice =
  let msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub skb) in
  let msg2 = enc(diff(make2(na,nb,pub skb),len2),r2,pub ska) in
  let msg3 = enc(diff(make3(nb,na),len3),r3,pub skb) in
  in(c,pk);
  out(c, if pk = pub skb then msg1 else enc(make1(na,pub ska),r1',pk));
  in(c,x);
  (* Last output of Alice, to which we add <na,nb> to model strong secrecy
     when the protocol completes and pk is honest, i.e. pk = pub skb. *)
  out(c, (* Cannot decrypt msg2: express result directly. *)
         if x = msg2 then (if pk = pub skb then <msg3,<na,nb>>) else
         if get2_na(dec(x,ska)) = na && get2_id(dec(x,ska)) = pk then
         (* Use alternate randomness for encryption. *)
         <enc(make3(get2_nb(dec(x,ska)),na), r3', pk),
          if pk = pub skb then <na,nb>>).

process Bob =
  let msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub skb) in
  let msg2 = enc(diff(make2(na, nb, pub skb),len2),r2,pub ska) in
  let msg3 = enc(diff(make3(nb,na), len3), r3, pub skb) in
  in(c,x);
  out(c, (* Cannot decrypt msg1: express result directly. *)
         if x = msg1 then msg2 else
         (* Cannot decrypt msg3: directly encode result (failed tag check). *)
         if x = msg3 then empty else
         if check_tag (dec(x,skb)) then
         enc(make2(get1_na(dec(x,skb)),
                   nb, pub skb),
             r2', get1_id(dec(x,skb)))).

system [NSL]
  (PUB : out(c, <pub(ska),pub(skb)>);
  ((A : Alice)|(B : Bob))).

(* We now explain why observational equivalence of NSL/left and /right
   implies the strong secrecy of na and nb: the output of these
   two nonces at the end of Alice can be replaced by two fresh names
   without the attacker being able to distinguish the two situations.

   Note that, in NSL/right, if we exclude the final output of `<na,nb>`:
   - assuming `pk = pub skb`,
     na only occurs in the last test and encryption of Alice;
   - nb only occurs in the last encryption of Bob.

   We could then prove, when `pk = pub skb`, the test
   `get2_na(dec(input@A1,ska)) = na` is always false by freshness of na
   at this point. This allows to prove that the final output of na
   is indistinguishable from a fresh name (it is actually a fresh name itself):
   thus na is strongly secret in NSL/right. By observational equivalence,
   it is also strongly secret in the real protocol NSL/left.

   Further, we only output `<na,nb>` at the end of Alice if `pk = pub skb`
   and the execution is successful:
     `input@A1 = msg2 || get2_na(dec(input@A1,ska)) = na`.
   We've seen that the second part is always false. Now, `input@A1 = msg2`
   can only hold if Bob sent that message (by IND-CCA2) hence `input@B = msg1`.
   Under our condition, we thus have no occurrence of `nb` on Bob's side,
   hence `nb` is also indistinguishable from a fresh name in the final output
   of `<na,nb>` by Alice. *)

(* It would also be good to model the strong secrecy of `nb` when Bob
   believes he's had a honest interaction with Alice -- this property fails in
   the original Needham-Schroeder protocol due to the man-in-the-middle attack.
   This would be modelled by outputting `nb` at the end of Bob's process when
   `get1_id(dec(input@B,skb)) = pub ska`. However, proving that this output
   is indistinguishable from a fresh name requires idealizing further the
   process, and introduce extra difficulties on Alice's side: we leave this
   more complete proof to future work, but note that these aspects are
   independent of CCA2 reasoning and bi-deduction. *)

(* ----------------------------------------------------------------------- *)

(* Because we apply CCA2 for each key ska and skb separately,
   we need to introduce an intermediate (bi)system:
   - NSL_a/left has real messages for outputs of Alice,
     but idealized ones for Bob's messages;
   - NSL_a/right is the same as NSL/right. *)

process Alice_a =
  let msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub(skb)) in
  let msg2 = enc(len2,r2, pub ska) in
  let msg3 = enc(diff(make3(nb,na), len3), r3, pub skb) in
  in(c,pk);
  out(c, if pk = pub skb then msg1 else enc(make1(na,pub ska),r1',pk));
  in(c,x);
  out(c, if x = msg2 then (if pk = pub skb then <msg3,<na,nb>>) else
         if get2_na(dec(x,ska)) = na && get2_id(dec(x,ska)) = pk then
         <enc(make3(get2_nb(dec(x,ska)),na), r3', pk),
          if pk = pub skb then <na,nb>>).

process Bob_a =
  let msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub(skb)) in
  let msg2 = enc(len2,r2,pub ska) in
  let msg3 = enc(diff(make3(nb,na), len3), r3, pub skb) in
  in(c,x);
  out(c, if x = msg1 then msg2 else
         if x = msg3 then empty else
         if check_tag (dec(x,skb)) then
         enc(make2(get1_na(dec(x,skb)),
                   nb, pub skb),
             r2', get1_id(dec(x,skb)))).

system [NSL_a]
  (PUB : out(c, <pub(ska),pub(skb)>);
  ((A : Alice_a)|(B : Bob_a))).

(* ----------------------------------------------------------------------- *)

(** Proofs *)

(* Dependency lemma for all systems. *)
lemma [NSL/left,NSL/right,NSL_a/left,NSL_a/right] depends_A_A1 :
  happens(A1) => A < A1.
Proof.
  intro _.
  project; try
  ((by use depends_NSL_A_A1 with A1) +
   (by use depends_NSL_a_A_A1 with A1)).
Qed.

(* Our current implementation of proof-search for bi-deduction cannot
   prove that `(frame@t,exec@t)` is bi-deducible (considering e.g.
   `NSL_a/left` and `NSL/right` on the right). We expect that this
   will be improved in the near future, by improving the inductive
   proof heuristic or allowing user control on it.

   For now we work around the limitation by proving the following technical
   lemma. It encodes a weak form of bi-deducibility as the existence of
   an adversarial function to which we explicitly pass the useful outputs
   of the CCA oracles. This simple (yet tedious) approach is only possible
   because we are in a simple situation where oracle calls can be
   performed at the beginning on data that is known in advance. *)
global lemma
  [NSL_a/left,NSL/right] deduction_right (t:timestamp[const])
  :
  Let msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub skb) in
  Let msg2 = enc(len2,r2,pub ska) in
  Let msg3 = enc(diff(make3(nb,na),len3),r3,pub skb) in
  Let fr =
    fun 
      (f: _ -> _ -> _ -> _ -> _ -> _ -> _ ->_ -> _ ->
        message*bool*message)
      (p:message)
      (m1:message)
      (m2:message)
      (m3:message)
      (ka:message)
      (na:message)
      (nb:message)
      (rand1:message)
      (rand3:message)    
    =>
      (f p m1 m2 m3 ka na nb rand1 rand3)#1
  in
  Let ex =
    fun 
     (f: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ ->
         message*bool*message) 
      (p:message)
      (m1:message)
      (m2:message)
      (m3:message)
      (ka:message)
      (na:message)
      (nb:message)
      (rand1:message)
      (rand3:message) 
    =>
      (f  p m1 m2 m3 ka na nb rand1 rand3)#2
  in
  Let pk =
    fun 
      (f: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ ->
         message*bool*message) 
      (p:message)
      (m1:message)
      (m2:message)
      (m3:message)
      (ka:message)
      (na:message)
      (nb:message)
      (rand1:message)
      (rand3:message)  
    =>
      (f p m1 m2 m3 ka na nb rand1 rand3)#3
  in
  [happens(t)] -> [t < B] ->
  Exists (f:_[adv]),
  [f (pub skb) msg1 msg2 msg3 ska na nb r1' r3' =
   (frame@t,exec@t,if A<=t then input@A)].
Proof.
  intro *.
  induction t.
  + rewrite /frame /exec.
    exists (fun (a,b,c,d,e,f,g,h,i:message) => (zero,true,zero)).
    by rewrite if_false.
  + destruct IH.
    rewrite /* and_true_r.
    exists (fun (p,m1,m2,m3,ka,na,nb,rand1,rand3:message) =>
      (<(fr f p m1 m2 m3 ka na nb rand1 rand3), 
       <of_bool ((ex f  p m1 m2 m3 ka na nb rand1 rand3)), 
       if (ex f  p m1 m2 m3 ka na nb rand1 rand3) then <pub ka, p>>>,
       (ex f  p m1 m2 m3 ka na nb rand1 rand3),
       (pk f  p m1 m2 m3 ka na nb rand1 rand3))).
    assert ((A <= PUB) <=> (A <= pred PUB)) as -> by auto.
    rewrite /= /fr /ex /pk /=. 
    rewrite /msg1 /msg2 /msg3 in H1.
    by rewrite H1.
  + destruct IH.
    rewrite /frame /exec /output /cond /msg1 /msg3 /input.
    rewrite and_true_r.
    exists  (fun (p,m1,m2,m3,ka,na,nb,rand1,rand3:message) =>
      (<(fr f p m1 m2 m3 ka na nb rand1 rand3),
        <of_bool (ex f  p m1 m2 m3 ka na nb rand1 rand3),
         if (ex f  p m1 m2 m3 ka na nb rand1 rand3) then
           if att (fr f  p m1 m2 m3 ka na nb rand1 rand3) = p
             then m1 else
           enc(make1(na,pub ka),rand1,att (fr f  p m1 m2 m3 ka na nb rand1 rand3))>>,
       (ex f  p m1 m2 m3 ka na nb rand1 rand3),
       att (fr f  p m1 m2 m3 ka na nb rand1 rand3))).
    rewrite (if_true (A <= A)); 1: auto.
    rewrite /fr /ex /=.
    rewrite /msg1 /msg2 /msg3 in H1.
    rewrite H1.
    rewrite (if_false (A <= pred A)); 1: auto.
    auto.
  + destruct IH.
    rewrite /frame /exec /output /cond /input /msg8 /msg2 /msg9 /msg3.
    rewrite and_true_r.
    exists (fun (p,m1,m2,m3,ka,na,nb,rand1,rand3:message) =>
      (<(fr f p m1 m2 m3 ka na nb rand1 rand3), 
       <of_bool (ex f p m1 m2 m3 ka na nb rand1 rand3), 
       if (ex f p m1 m2 m3 ka na nb rand1 rand3)  then
            (if att (fr f p m1 m2 m3 ka na nb rand1 rand3) = m2 
	     then (if (pk f p m1 m2 m3 ka na nb rand1 rand3) = p 
	     then <m3,<na,nb>>) else
             if get2_na (dec (att (fr f p m1 m2 m3 ka na nb rand1 rand3), ka)) = na &&
                get2_id (dec (att (fr f p m1 m2 m3 ka na nb rand1 rand3), ka)) = 
                (pk f p m1 m2 m3 ka na nb rand1 rand3)
           then
               <enc
                  (make3 (get2_nb (dec (att (fr f p m1 m2 m3 ka na nb rand1 rand3), ka)), na),
                   rand3,
                   (pk f p m1 m2 m3 ka na nb rand1 rand3)),
                if (pk f p m1 m2 m3 ka na nb rand1 rand3) = p then <na,nb>>)>>,
        (ex f p m1 m2 m3 ka na nb rand1 rand3),
        (pk f p m1 m2 m3 ka na nb rand1 rand3))).
    assert A < A1 by use depends_A_A1.
    assert (A <= A1) <=> (A <= pred A1) as -> by auto.
    rewrite /fr /ex /pk /input. 
    rewrite /msg1 /msg2 /msg3 in H1.
    rewrite /= H1. 
    reduce ~flags:[diffr].
    by rewrite (if_true (A <= pred A1)).
  + by rewrite lt_irrefl in H0.
Qed.

(* Similar to deduction_right but for NSL/left and NSLFixedka/left.
   Better multi-system reasoning in Squirrel should allow to
   merge the two lemmas. *)
global lemma [NSL/left,NSL_a/left] deduction_left (t:timestamp[const]) :
  Let msg1 = enc(make1(na,pub(ska)),r1,pub skb) in
  Let msg2 = enc(diff((make2(na, nb, pub skb)),len2),r2,pub ska) in
  Let msg3 = enc(make3(nb,na),r3,pub skb) in
  Let fr =
    fun (f: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _-> message*bool*message)
      (p:message)
      (m1:message)
      (m2:message)
      (m3:message)
      (kb:message)
      (na:message)
      (nb:message)
      (rand1:message)
      (rand2:message)
     =>
    (f p m1 m2 m3 kb na nb rand1 rand2)#1
  in
  Let ex =
    fun (f: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _-> message*bool*message) 
        (p:message)
    	(m1:message)
    	(m2:message)
    	(m3:message)
    	(kb:message)
      (na:message)
    	(nb:message)
      (rand1:message)
      (rand2:message)
    =>
      (f p m1 m2 m3 kb na nb rand1 rand2)#2
  in
  Let pk =
    fun (f: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _-> message*bool*message) 
      (p:message)
      (m1:message)
      (m2:message)
      (m3:message)
      (kb:message)
      (na:message)
      (nb:message)
      (rand1:message)
      (rand2:message)
    =>
      (f p m1 m2 m3 kb na nb rand1 rand2)#3
  in
  [happens(t)] -> [t < A1] ->
  Exists (f:_[adv]),
  [f (pub ska) msg1 msg2 msg3 skb na nb r1' r2' =
   (frame@t,exec@t,if A<=t then input@A)].
Proof.
  intro *.
  induction t.
  + rewrite /frame /exec.
    exists (fun (a,b,c,d,e,f,g,h,i:message) => (zero,true,zero)).
    by rewrite if_false.
  + destruct IH.
    rewrite /* and_true_r.
    exists (fun (p,m1,m2,m3,kb,na,nb,rand1,rand2:message) =>
      (<(fr f p m1 m2 m3 kb na nb rand1 rand2),
       <of_bool (ex f p m1 m2 m3 kb na nb rand1 rand2),
       if (ex f p m1 m2 m3 kb na nb rand1 rand2) 
       then <p, pub kb>>>,
      ( ex f p m1 m2 m3 kb na nb rand1 rand2),
      (pk f p m1 m2 m3 kb na nb rand1 rand2))).
    assert (A <= PUB) <=> (A <= pred PUB) as -> by auto.
    rewrite /msg1 /msg2 /msg3 in H1.
    by rewrite /fr /ex /pk /= H1.
  + destruct IH.
    rewrite /frame /exec /output /cond /msg1 /msg3.
    rewrite and_true_r.
    exists  (fun (p,m1,m2,m3,kb,na,nb,rand1,rand2:message) =>
      (<(fr f p m1 m2 m3 kb na nb rand1 rand2),
        <of_bool (ex f p m1 m2 m3 kb na nb rand1 rand2),
         if (ex f p m1 m2 m3 kb na nb rand1 rand2) then
           if att (fr f p m1 m2 m3 kb na nb rand1 rand2) = pub kb then m1 else
           enc(make1(na,p),rand1,att (fr f p m1 m2 m3 kb na nb rand1 rand2))>>,
       (ex f p m1 m2 m3 kb na nb rand1 rand2),
       att (fr f p m1 m2 m3 kb na nb rand1 rand2))).
    rewrite /* in *.
    rewrite /= H1.
    by rewrite (if_true (A <= A)).
  + by rewrite lt_irrefl in H0.
  + destruct IH.
    rewrite /* and_true_r.
    exists (fun (p,m1,m2,m3,kb,na,nb,rand1,rand2:message) =>
      (<(fr f  p m1 m2 m3 kb na nb rand1 rand2)
       , <of_bool (ex f  p m1 m2 m3 kb na nb rand1 rand2),
        if (ex f  p m1 m2 m3 kb na nb rand1 rand2)  then
          if att (fr f  p m1 m2 m3 kb na nb rand1 rand2) = m1 then m2 else
          if att (fr f  p m1 m2 m3 kb na nb rand1 rand2) = m3 then empty else
          if check_tag (dec (att (fr f p m1 m2 m3 kb na nb rand1 rand2), kb)) then
             enc (make2
                  (get1_na (dec (att (fr f p m1 m2 m3 kb na nb rand1 rand2), kb)),
                   nb, pub kb),
                rand2,
                get1_id (dec (att (fr f  p m1 m2 m3 kb na nb rand1 rand2), kb)))
           >>, 
       (ex f  p m1 m2 m3 kb na nb rand1 rand2),
       (pk f  p m1 m2 m3 kb na nb rand1 rand2))).
    rewrite /* /= in *. 
    assert (A <= B) <=> (A <= pred B) as -> by auto.
    by rewrite H1.
Qed.

(* ----------------------------------------------------------------------- *)

(* Prove a (strengthened form of) observational indistinguishability
   between NSL_a/left and NSL/right (= NSL_a/right).
   Note that we can reveal na and nb as we are only working
   wrt a CCA2 attacker. *)
global lemma [NSL_a/left,NSL/right] equiv_right (t:timestamp[const]) :
  Let msg1 = enc( diff(make1(na,pub(ska)),len1),r1,pub(skb)) in
  Let msg2 = enc(len2, r2, pub ska) in
  Let msg3 = enc(diff(make3(nb,na), len3), r3, pub skb) in
  [happens(t)] ->
  equiv(msg1,msg2,msg3,pub skb,
        ska, na, nb, r1', r3',
        frame@t).
Proof.
  intro *.
  induction t.
  + rewrite /*.
    crypto CCA2 (key :skb).
    by rewrite len3.
    by rewrite len1.
  + rewrite /* in *.
    apply IH.
  + rewrite /* in *.
    apply IH.
  + rewrite /* in *.
    fa !<_,_>.
    apply IH.
  + rewrite /*.
    fa !<_,_>.
    fa if _ then _.
    have Hf := deduction_right (pred B).
    simpl ~zeta.
    have Hap : happens(pred B) by auto.
    apply Hf in Hap; 1: auto.
    clear Hf.
    destruct Hap as [f Hf].
    assert frame@pred B = (f (pub skb) msg1 msg2 msg3 ska na nb r1' r3')#1 as ->
      by rewrite Hf.
    rewrite /msg1 /msg2 /msg3.
    crypto CCA2 (key:skb) => //.
    * auto ~flags:[diffr].
    * auto ~flags:[diffr].
    * by rewrite len3.
    * by rewrite len1.
Qed.

(* ----------------------------------------------------------------------- *)

(* Observational equivalence between NSL/left and NSL_a/left. *)
global lemma [NSL/left,NSL_a/left] equiv_left (t:timestamp[const]) :
  Let msg1 = enc(make1(na,pub(ska)),r1,pub skb) in
  Let msg2 = enc(diff((make2(na, nb, pub skb)),len2),r2,pub ska) in
  Let msg3 = enc(make3(nb,na),r3,pub skb) in
  [happens(t)] ->
  equiv(msg1,msg2,msg3, pub ska,
        skb, na, nb, r1', r2',
        frame@t).
Proof.
  intro *.
  induction t.
  + rewrite /*.
    crypto CCA2 (key :ska).
    by rewrite len2.
  + rewrite /*in *.
    apply IH.
  + rewrite /*in *.
    apply IH.
  + assert A < A1 by use depends_A_A1.
    rewrite /*.
    fa !<_,_>, if _ then _.
    have Hf := deduction_left (pred A1).
    simpl ~zeta.
    have Hap : happens(pred A1) by auto.
    apply Hf in Hap; 1: auto.
    clear Hf.
    destruct Hap as [f Hf].
    assert frame@pred A1 = (f (pub ska) msg1 msg2 msg3 skb na nb r1' r2')#1 as ->
      by rewrite Hf.
    assert att (frame@pred A) = (f (pub ska) msg1 msg2 msg3 skb na nb r1' r2')#3 as ->
      by rewrite Hf (if_true (A <= pred A1)).
    rewrite /msg1 /msg2 /msg3.
    crypto CCA2 (key:ska) => //.
    * by project.
    * by rewrite len2.
  + rewrite /* in *.
    apply IH.
Qed.

(* ------------------------------------------------------------------------ *)

(* We finally prove that the two projections of the bi-system NSL
   are observationally equivalent, by transitivity. *)

(* Immediate consequence of equiv_left. *)
global lemma
  [set: NSL; equiv:NSL/left,NSL_a/left]
  equiv_left_sys (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro *.
  trans [NSL/left,NSL_a/left].
  + auto.
  + by apply equiv_left.
  + auto.
Qed.

(* Immediate consequence of equiv_right. *)
global lemma
  [set:NSL; equiv:NSL_a/left,NSL/right]
  equiv_right_sys (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro *.
  trans [NSL_a/left,NSL/right].
  + auto.
  + by apply equiv_right.
  + auto.
Qed.

global theorem [NSL] nsl_security (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro *.
  trans [NSL_a/left,NSL_a/left].
  + by apply equiv_left_sys.
  + auto.
  + by apply equiv_right_sys.
Qed.
