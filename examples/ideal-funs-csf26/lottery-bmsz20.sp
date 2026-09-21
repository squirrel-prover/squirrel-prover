(* This file models the Anonymous lottery functionality from [BMSZ20].

It  proves that the ideal functionality is indeed anonymous. 

[BMZ20]: F. Baldimtsi, V. Madathil, A. Scafuro, and L. Zhou, “Anonymous
lottery in the proof-of-stake setting,” in 33rd IEEE Computer Security
Foundations Symposium (CSF 2020), 2020, pp. 318–333.
*)


(*******************************************************************)
(***            Genric function declarations                   *****)
(*******************************************************************)

include Core.

(* The set of parties *)

(* We assume that each party name P_i is an index, which is a builtin abstract set of elements. *) 

(* We declare an encoding function from  index to messages. *)
abstract party : index -> message.

(* We declare the function which tells if a party is honest or not. *)
abstract honest_party : index -> bool.

(* Function associating to each party its stake. *)
abstract stake : index -> message.

(* We define the global message buffer L. *)
mutable L : message = zero.

abstract append : (message * index * message) * message -> message.

(* Functions for Pids. *)
abstract pid : index -> message.
abstract honest_pid : message -> bool.


(* Eli states and LE  predicate *)

(* We declare a type which is either a boolean or undefined. *)
type bool_undef [serializable].

abstract undef : bool_undef.
abstract dtrue : bool_undef.
abstract dfalse : bool_undef.
axiom [any] bu1:
  dfalse <> dtrue.


(* The Eli states, initialized to undef. *)
mutable Eli0_hon (pid,e:index) : bool_undef = undef.
mutable Eli1_hon (pid,e:index) : bool_undef = undef.
mutable Eli_dis (pid,e:index) : bool_undef = undef.

abstract Elligible : message  * message * index -> bool_undef.

abstract LE : message * message -> bool_undef.

(* Squirrel models network communications as happening over channels, we declare a dummy one. *)
channel pub.

abstract decode_bool : message -> bool.
abstract encode_bool : bool_undef -> message.
abstract decode_e : message -> index.


abstract r : index * index  -> message.

(* Declare a mutex to make sub-processes atomic *)
mutex l : 0

(*******************************************************************)
(***             Process/oracle declarations                   *****)
(*******************************************************************)

(* We declare for each oracle a corresponding process. *)

(* i' is the replication index, which allows to run the oracle an unbounded number of time. *)
process OEligibilitycheck(i':index, tag:index, i:index) =
  lock l;
  in(pub, x);  (* x=(sid, (tag, (pid,beta'))) *)
  (* Modeling detail: we do not in fact consider that the value tag
  is received over the network, but rather for each possible tag we
  spawn an unbounded number of oracle willing to run for this value
  of the tag. The attacker can then choose the oracle with the tag
  value it wants. This is only because we need to put the tag as a
  parameter of the mutable state, which cannot yet be done in
  Squirrel for values received over the network, but only for
  replication indices. *)
  let sid = fst(x) in
  (* let tag = decode_e(fst(snd(x))) in *)
  let pidi = fst(snd(snd(x))) in
  let beta = decode_bool(snd(snd(snd(x)))) in

  if pidi = pid(i) && honest_pid(pidi) then
    Eli0_hon i tag := 
      if beta = false && Eli0_hon i tag = undef then
        Elligible(r(i', tag), stake i, tag)
      else
        Eli0_hon i tag;
    Eli1_hon i tag :=
      if beta = true && Eli1_hon i tag = undef then
        Elligible(r(i', tag), stake i, tag)
      else 
        Eli1_hon i tag;
    unlock l
  else
    unlock l.

abstract e_mess : index->message.

abstract PROOF1: index*message -> message.
abstract PROOF2: message*index*message -> message.

process OCreateProof(i':index, tag:index, i,j:index) =
  lock l;
  in(pub, x);  (* x=(sid, (tag, (msg,pidi))) *)
  let sid = fst(x) in
(*let tag = fst(snd(x)) in *)
  let msg = fst(snd(snd(x))) in     
  let pidi = fst(snd(snd(snd(x)))) in     
  let pidj = snd(snd(snd(snd(x)))) in     

  if pidi = pid i && honest_pid pidi &&
                         pidj = pid j && honest_pid pidj &&
                         Eli0_hon i tag <> undef &&
                         Eli1_hon j tag <> undef &&
                         Eli0_hon i tag = Eli1_hon j tag &&
                         diff(Eli0_hon i tag, Eli1_hon j tag) = dtrue  then
    out(pub, PROOF1(tag,msg) );
    unlock l;
    lock l;
    in(pub, y);  (* y = (DONE, (psi, (tag',msg))) *)
    let pi = fst(snd(x)) in
    let tag' = fst(snd(snd(x))) in     
    let msg' = snd(snd(snd(x))) in     
    L := append( (pi,tag,msg), L);
    out(pub, PROOF2(pi,tag,msg));
    unlock l
  else
    unlock l.


abstract is_in : message * index * message * message -> bool.

abstract VERIFY : message * message * index * message -> message.

process OVerify(i':index, tag:index, i:index) =
  lock l;
  in(pub, x);  (* x=(sid, (pi, (tag, (msg,pidi)))) *)
  let sid = fst(x) in
  let pi = fst(snd(x)) in
(*let tag = fst(snd(snd(x))) in *)
  let msg = fst(snd(snd(snd(x)))) in     
  let pidi = snd(snd(snd(snd(x)))) in     
  if pidi = pid i && not(honest_pid pidi) &&
                       not( is_in(pi,tag,msg,L)) then
    out(pub, VERIFY(sid, pi, tag,msg) );
    unlock l;
    !_j
    lock l;
    in(pub, w);  (* w = (pidj, tag',msg')  *)
    let pidj = fst(x) in
    let tag' = fst(snd(x)) in     
    let msg' = snd(snd(x)) in     
    if pidj = pid j && not(honest_pid pidj) &&
      Eli_dis i tag = dtrue then
      L := append( (pi,tag,msg), L);
      unlock l
    else
      unlock l
  else
    unlock l.


process OEligibilitycheckCorrupted(i':index, tag:index, i:index) =
  lock l;
  in(pub, x);  (* x=(sid, (tag, (pid))) *)
  let sid = fst(x) in
  (* let tag = decode_e(fst(snd(x))) in *)
  let pidi = snd(snd(x)) in
  if pidi= pid i && not(honest_pid pidi) && Eli_dis i tag =undef then
    Eli_dis i tag :=  Elligible(r(i', tag), stake i, tag);
    out(pub, encode_bool(Elligible(r(i', tag), stake i, tag)));
    unlock l
  else
    unlock l.




process OCreateProofCorrupted(i':index, tag:index, i,j:index) =
  lock l;
  in(pub, x);  (* x=(sid, (tag, (msg,pidi))) *)
  let sid = fst(x) in
(*let tag = fst(snd(x)) in *)
  let msg = fst(snd(snd(x))) in     
  let pidi = snd(snd(snd(x))) in         

  if pidi = pid i && not(honest_pid pidi) &&
                         Eli_dis i tag = dtrue then

    out(pub, PROOF1(tag,msg) );
    unlock l;
    lock l;
    in(pub, y);  (* y = (DONE, (psi, (tag',msg))) *)
    let pi = fst(snd(x)) in
    let tag' = fst(snd(snd(x))) in     
    let msg' = snd(snd(snd(x))) in     
    L := append( (pi,tag,msg), L);
    out(pub, PROOF2(pi,tag,msg));
    unlock l
  else
    unlock l.


abstract Verified  : message*message*index*message *bool -> message.
process OVerifyCorrupted(i':index, tag:index, i:index) =
  lock l;
  in(pub, x);  (* x=(sid, (pi, (tag, (msg,pidi)))) *)
  let sid = fst(x) in
  let pi = fst(snd(x)) in
(*let tag = fst(snd(snd(x))) in *)
  let msg = fst(snd(snd(snd(x)))) in     
  let pidi = snd(snd(snd(snd(x)))) in     
  if pidi = pid i && not(honest_pid pidi) &&
                       not( is_in(pi,tag,msg,L)) then
    out(pub, VERIFY(sid, pi, tag,msg) );
    unlock l;
    !_j
    lock l;
    in(pub, w);  (* w = (pidj, tag',msg')  *)
    let pidj = fst(x) in
    let tag' = fst(snd(x)) in     
    let msg' = snd(snd(x)) in     
    if pidj = pid j && not(honest_pid pidj) &&
      Eli_dis j tag = dtrue then
      L := append( (pi,tag,msg), L);
      out(pub, Verified(sid,pi,tag,msg,true));
      unlock l
    else
      unlock l
  else
    unlock l.



(* The full system declaration, over which we will prove that its two diff projections are equivalent. *)
system !_i' !_tag !_P (
  !_i OEligibilitycheck(i',tag,i) |
  !_i !_j OCreateProof(i',tag,i,j) |
  !_i OVerify(i',tag,i) |
  !_i OEligibilitycheckCorrupted(i',tag,i) |
  !_i !_j OCreateProofCorrupted(i',tag,i,j) |
  !_i OVerifyCorrupted(i',tag,i)
).

(*******************************************************************)
(***            Lemmas                                         *****)
(*******************************************************************)

global lemma caseL (u,v:timestamp) :
[u<v] -> [u=pred(v) || u < pred(v)].
Proof.
intro U.
auto.
Qed.

global lemma public_past  (t,t':timestamp[const]) :
  [t < t'] -> Exists (f : message -> message [adv]),
 [frame@t = f (frame@t')].
Proof.
 intro Neq.


 induction t';
   try (have U := caseL _ _ Neq;
     case U;  [1:exists (fun x  => fst x); auto |
     2:have IH' := IH _ => //;
     destruct IH';  exists (fun x  => f (fst x)); auto ] ).

   + exists (fun x  => zero). auto.   
Qed.

global lemma public_L  (t:timestamp[const], tag:index [const,glob]) :
  [happens(t)] -> Exists (f : message -> message [adv]),
 [L@t = f (frame@t)].
Proof.
  intro H.
  induction t;       try  (destruct IH; exists (fun x => f (fst x)); expand L,frame; rewrite H0; auto).

 + exists (fun x  => zero). auto.  



 +  expandall.   destruct IH.

   depends (OCreateProof(i', tag0, P, i, j)), (OCreateProof1(i', tag0, P, i, j)).     auto.
   intro U.
   have past := public_past (pred (OCreateProof(i', tag0, P, i, j))) (pred (OCreateProof1(i', tag0, P, i, j))) _ .  auto.
   destruct past.


    exists (fun x =>
     append
     ((fst (snd (att (f0 (fst x)  ))),
       tag0,
       fst (snd (snd (att ( f0 (fst x) ))))),
       f ( fst x)
)
    ). rewrite H0 H1.  auto. 


 +  expandall.   destruct IH.

   depends (OVerify(i', tag0, P, i)), (OVerify1(i', tag0, P, i, j)).     auto.
   intro U.
   have past := public_past (pred (OVerify(i', tag0, P, i))) (pred (OVerify1(i', tag0, P, i, j))) _ .  auto.
   destruct past.


    exists (fun x =>
     append
     ((fst (snd (att (f0 (fst x)  ))),
       tag0,
       fst (snd (snd (snd (att ( f0 (fst x) )))))),
       f ( fst x)
)
    ). rewrite H0 H1.  auto. 

 +  expandall.   destruct IH.

   depends (OCreateProofCorrupted(i', tag0, P, i, j)), (OCreateProofCorrupted1(i', tag0, P, i, j)).     auto.
   intro U.
   have past := public_past (pred (OCreateProofCorrupted(i', tag0, P, i, j))) (pred (OCreateProofCorrupted1(i', tag0, P, i, j))) _ .  auto.
   destruct past.


    exists (fun x =>
     append
     ((fst (snd (att (f0 (fst x)  ))),
       tag0,
       fst (snd (snd (att ( f0 (fst x) ))))),
       f ( fst x)
)
    ). rewrite H0 H1.  auto. 



 +  expandall.   destruct IH.

   depends (OVerifyCorrupted(i', tag0, P, i)), (OVerifyCorrupted1(i', tag0, P, i,j)).     auto.
   intro U.
   have past := public_past (pred (OVerifyCorrupted(i', tag0, P, i))) (pred (OVerifyCorrupted1(i', tag0, P, i, j))) _ .  auto.
   destruct past.


    exists (fun x =>
     append
     ((fst (snd (att (f0 (fst x)  ))),
       tag0,
       fst (snd (snd (snd (att ( f0 (fst x) )))))),
       f ( fst x)
)
    ). rewrite H0 H1.  auto. 
Qed.





global lemma public_dis  (t:timestamp[const], tag:index [const,glob]) :
  [happens(t)] -> Exists (f : message -> index -> bool_undef [adv]),
 [forall i, Eli_dis i tag@t = f (frame@t) i]

.
Proof.
   intro H.
   induction t;
      (* for all created subgoal, why try the trival proof where the state is not touched by the action. *)
      try  (destruct IH; exists (fun x => f (fst x)); expand Eli_dis,frame; rewrite H0; auto).
 
 + exists (fun x i => undef). auto.   

+ expandall. destruct IH.
  exists (fun x i0 => 
  if i = i0 && tag = tag0 then  Elligible( r(i',tag0), stake i, tag0) else f (fst x) i0). rewrite H0.  intro i0.  simpl ~flags:beta. fa; auto.
Qed.


global lemma public_eli0  (t:timestamp[const], tag:index [const,glob]) :
  [happens(t)] -> Exists (f : message -> index -> bool_undef [adv]),
[forall i, Eli0_hon i tag@t = f (frame@t) i].
Proof.
  intro H.

   induction t; 
      (* for all created subgoal, why try the trival proof where the state is not touched by the action. *)
      try  (destruct IH; exists (fun x => f (fst x)); expand Eli0_hon,frame; rewrite H0; auto).
 
 + exists (fun x i => undef). auto.   

  + destruct IH. expand frame. expand exec. expand Eli0_hon,beta.
 

   exists (fun x i0 => 
if i = i0 && tag = tag0 then
  if decode_bool (snd (snd (snd (att (fst x)  (* input@OLottery(i', e0, P, i0) *) )))) =
          false && f (fst x) i = undef  then
          Elligible( r(i',tag0), stake i, tag0)

      else  f (fst x) i (* Eli0 with H0 *)
  else  f(fst x) i0 ) (* Eli0 with H0 *)
.

 rewrite H0. intro i0. 
reduce ~flags:beta. rewrite fst_pair.   fa => //.  intro [A B] [C D]. subst tag, tag0. rewrite H0. auto.

Qed.

global lemma public_eli1  (t:timestamp[const], tag:index [const,glob]) :
  [happens(t)] -> Exists (f : message -> index -> bool_undef [adv]),
[forall i, Eli1_hon i tag@t = f(frame@t) i].
Proof.
  intro H.

   induction t; 
      (* for all created subgoal, why try the trival proof where the state is not touched by the action. *)
    try  (destruct IH; exists (fun x => f (fst x)); expand Eli1_hon,frame; rewrite H0; auto).
 
 + exists (fun x i => undef). auto.   

  + destruct IH. expand frame. expand exec. expand Eli1_hon,beta.
 

   exists (fun x i0 => 
if i = i0 && tag = tag0 then
  if decode_bool (snd (snd (snd (att (fst x)  (* input@OLottery(i', e0, P, i0) *) )))) =
          true && f(fst x) i = undef  then
                 Elligible( r(i',tag0), stake i, tag0)
      else  f(fst x) i(* Eli0 with H0 *)
  else  f(fst x) i0)(* Eli0 with H0 *)
.

 rewrite H0. intro i0. 
reduce ~flags:beta. rewrite fst_pair.   fa => //.  intro [A B] [C D]. subst tag, tag0. rewrite H0. auto.
Qed.


(*******************************************************************)
(***            Security Theorem                               *****)
(*******************************************************************)

(* The final indistinguishability goal, where `equiv` directly asks to
prove that the given system is diff-equivalent. *) 
equiv lotteryprivacy.
Proof.
  induction t.
  
  +  auto.

  + expandall. fa 0 => //. 

  + expandall. fa 0 => //. 


 + expand frame, exec, cond,output. fa 0; fa 1. fa 2. rewrite /msg. 
   have Eq : (forall (x,y:bool_undef), (x=y && diff(x,y) = dtrue) <=> (x = dtrue && y=dtrue) ).
   
  project; intro x y; split; auto.

  rewrite Eq in 1.
  expand pidi1, pidj.

  

  use public_eli0 with pred(OCreateProof(i', tag, P, i, j)), tag. destruct H0.  rewrite H0.
  use public_eli1 with pred(OCreateProof(i', tag, P, i, j)), tag. destruct H1. rewrite H1.

  deduce 1 => //.
  auto. auto.

 + expand frame, exec, cond,output,pi,msg. fa 0; fa 1.  fa 1. by deduce 1.

 + expand frame, exec, cond,output. fa 0; fa 1.  
   have Eq : (forall (x,y:bool_undef), (x=y && diff(x,y) = dtrue) <=> (x = dtrue && y=dtrue) ).
   
  project; intro x y; split; auto.

  rewrite Eq in 1.
  expand pidi1, pidj. fa 1. 


  use public_eli0 with pred(OCreateProof2(i', tag, P, i, j)), tag. destruct H0. rewrite H0.
  use public_eli1 with pred(OCreateProof2(i', tag, P, i, j)), tag. destruct H1. rewrite H1.

  deduce 1 => //.
  auto. auto.

  + expand frame,exec, cond,output, pi1, msg1,sid2, pidi2. 

  use public_L with pred (OVerify(i', tag, P, i)). destruct H0. rewrite H0.
  fa 0.
  by deduce 1.
  auto.

  + expandall.  
  use public_dis with pred(OVerify1(i', tag, P, i, j)), tag. destruct H0. rewrite H0.
  fa 0 => //.  auto.


  + expandall.  
  use public_dis with pred(OVerify2(i', tag, P, i, j)), tag. destruct H0. rewrite H0.
  fa 0 => //.  auto.

  + expandall.  

  use public_L with pred (OVerify3(i', tag, P, i)). destruct H0. rewrite H0.
  fa 0 => //.  auto.

  + expandall.  
  use public_dis with pred(OEligibilitycheckCorrupted(i', tag, P, i)), tag. destruct H0. rewrite H0.
  fa 0 => //.  auto.

  + expandall.  
  use public_dis with pred(OEligibilitycheckCorrupted1(i', tag, P, i)), tag. destruct H0. rewrite !H0.
  fa 0 => //.  auto.

  + expandall.  
  use public_dis with pred(OCreateProofCorrupted(i', tag, P, i, j)), tag. destruct H0. rewrite !H0.
  fa 0 => //.  auto.

  + expandall.  fa 0 => //. 


  + expandall.  

  use public_dis with pred(OCreateProofCorrupted2(i', tag, P, i, j)), tag. destruct H0. rewrite !H0.
  fa 0 => //.  auto.



  + expandall.

  use public_L with pred (OVerifyCorrupted(i', tag, P, i)). destruct H0. rewrite H0.
  fa 0.
  by deduce 1.
  auto.


  + expandall.  
  use public_dis with pred(OVerifyCorrupted1(i', tag, P, i,j)), tag. destruct H0. rewrite H0.
  fa 0 => //.  auto.


  + expandall.  
  use public_dis with pred(OVerifyCorrupted2(i', tag, P, i, j)), tag. destruct H0. rewrite !H0.
  fa 0 => //.  auto.

 + expandall.
  use public_L with pred (OVerifyCorrupted3(i', tag, P, i)). destruct H0. rewrite !H0.
  fa 0 => //.  auto.
Qed.
