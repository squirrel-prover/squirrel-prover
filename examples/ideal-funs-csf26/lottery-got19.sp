(* This file models the Anonymous lottery functionality from [GOT19].

It  proves that the ideal functionality is indeed anonymous. 

[GOT19]: C. Ganesh, C. Orlandi, and D. Tschudi, “Proof-of-stake protocols for
privacy-aware blockchains,” in 38th Annual International Conference
on the Theory and Applications of Cryptographic Techniques (EURO-
CRYPT 2019), ser. Lecture Notes in Computer Science. Springer, 2019,
pp. 690–719.
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


(* We define the message buffer Buffer(k) owned by party with name party(k). *)
mutable Buffer( k : index) : message = zero.

abstract append : message * message -> message.

(* The set of pids for stakeholders *)

(* The set of stakeholders is also an index. *)

abstract pid : index -> message.

abstract honest_pid : message -> bool.

abstract pid_alpha : index -> message.

(* we must assume that the function is injective. *)
exact axiom [any] pid_inj (A, B:index) :
  (pid(A) = pid(B)) = (A = B).
hint rewrite pid_inj.


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

abstract LE : message * message -> bool_undef.

(* Squirrel models network communications as happening over channels, we declare a dummy one. *)
channel pub.

abstract decode_bool : message -> bool.
abstract decode_e : message -> index.


abstract r : index * index  -> message.

(* Declare a mutex to make each oracle atomic *)
mutex l : 0.

(*******************************************************************)
(***             Process/oracle declarations                   *****)
(*******************************************************************)

(* We declare for each oracle a corresponding process. *)

(* OLottery*)
(* i' is the replication index, which allows to run the oracle an unbounded number of time. *)
process OLottery(i':index, e:index, i:index) =
  lock l;
  in(pub, x);  (* x=(sid, (e, (pid,beta))) *)
  let sid = fst(x) in
  (* let e = decode_e(fst(snd(x))) in *)
  (* Modeling detail: we do not in fact consider that the value tage
  is received over the network, but rather for each possible e we
  spawn an unbounded number of oracle willing to run for this value
  of the tag. The attacker can then choose the oracle with the e
  value it wants. This is only because we need to put the e as a
  parameter of the mutable state, which cannot yet be done in
  Squirrel for values received over the network, but only for
  replication indices. *)
  let pidi = fst(snd(snd(x))) in
  let beta = decode_bool(snd(snd(snd(x)))) in
  if pidi = pid(i)  && honest_pid(pidi) then
    Eli0_hon i e := 
      if beta = false && Eli0_hon i e = undef then
        LE(pid_alpha(i),r(i', e))
      else
        Eli0_hon i e;
    Eli1_hon i e :=
      if beta = true && Eli1_hon i e = undef then
        LE(pid_alpha(i),r(i',e))
      else 
        Eli1_hon i e;
    unlock l
  else
    unlock l.


abstract e_mess : index->message.

process OSend(i':index, e:index, P:index, i,j:index) =
  lock l;
  in(pub, x);  (* x=(sid, (e, (msg,(pidi,(pidj,P))))) *)
  let sid = fst(x) in
(*let e_mess = fst(snd(x)) in
  let e = decode_e(e_mess) in *)
  let msg = fst(snd(snd(x))) in     
  let pidi = fst(snd(snd(snd(x)))) in     
  let pidj = fst(snd(snd(snd(snd(x))))) in     
(*let P = fst(snd(snd(snd(snd(x))))) in      *)
  if pidi = pid i && honest_pid pidi &&
                         pidj = pid j && honest_pid pidj &&
                         Eli0_hon i e <> undef &&
                         Eli1_hon j e <> undef &&
                         Eli0_hon i e = Eli1_hon j e &&
                         diff(Eli0_hon i e, Eli1_hon j e) = dtrue  then
  (* Modeling detail: instead of updating all buffers. 
     We in fact allow the attacker to chose P, 
     the oracle is at least as powerful as the general one. *)
    Buffer(P) := append(<e_mess e,msg>, Buffer(P));
    out(pub, < sid, <e_mess e,msg>>);
    unlock l
  else
    unlock l.

abstract bool_of_mess : message -> bool.

process OFetchNew(i':index, Pi:index) =
  lock l;
  in(pub, x);  (* (sid, (Pi, Beta')) *)
  let sid = fst(x) in
(* let Pi = fst(snd(x)) in *)
  let beta' = bool_of_mess(snd(snd(x))) in
  Buffer Pi := 
    if honest_party Pi && diff(beta'=false, beta'=true) then
      zero
    else
      Buffer(Pi);
  unlock l.

abstract r' : index * index  -> message.

process OLotteryCorrupted(i':index, e:index,i:index) =
  lock l;
  in(pub, x);  (* (sid, (e, pidi)) *)
  let sid = fst(x) in
(*  let e_mess = fst(snd(x)) in
  let e = decode_e(e_mess) in *)
  let pidi = snd(snd(x)) in
  if pidi= pid i && not(honest_pid pidi) && Eli_dis i e=undef then
    Eli_dis i e := LE(pid_alpha(i),r'(i',e));
    unlock l
  else
    unlock l.


process OSendCorrupted(i':index, e:index, P : index, i:index) =
  lock l;
  in(pub, x);  (* (sid, (e, (msg,(pidi,P)))) *)
  let sid = fst(x) in
  (* let e_mess = fst(snd(x)) in
  let e = decode_e(e_mess) in *)
  let msg = fst(snd(snd(x))) in
  let pidi = fst(snd(snd(snd(x)))) in
  (* let P = snd(snd(snd(snd(x)))) in *)
  if pidi= pid i && not(honest_pid pidi) &&  Eli_dis i e=dtrue then
    Buffer(P) := append(<e_mess e,msg>, Buffer(P));
    out(pub, < sid, <e_mess e,msg>>); (* typo in pdf msg->m *)
    unlock l
  else
    unlock l


process OFetchNewCorrupted(i':index, Pi:index) =
  lock l;
  in(pub, x);  (* (sid, Pi) *)
  let sid = fst(x) in
(*  let Pi = snd(x) in *)
  if not(honest_party Pi) then
    Buffer(Pi) := zero;
    out(pub, Buffer(Pi));
    unlock l
  else
    unlock l.  

process OGetStakecorrupted(i':index, i:index) =
  lock l;
  in(pub, x);  (* (sid, pidi) *)
  let sid = fst(x) in
  let pidi = snd(x) in
  if pidi = pid i && not(honest_pid pidi) then
    out(pub, pid_alpha i);
    unlock l
  else
    unlock l.

(* The full system declaration, over which we will prove that its two diff projections are equivalent. *)
system !_i' !_e !_P (
  !_i OLottery(i',e,i) |
  !_i !_j OSend(i',e,P,i,j) |
  OFetchNew(i',P) |
  !_i OLotteryCorrupted(i',e,i) |
  !_i OSendCorrupted(i',e,P,i) |
  OFetchNewCorrupted(i',P) |
  !_i OGetStakecorrupted(i',i)
).


(*******************************************************************)
(***            Lemmas                                         *****)
(*******************************************************************)

global lemma public_dis  (t:timestamp[const], e:index [const,glob]) :
  [happens(t)] -> Exists (f : message -> index -> bool_undef [adv]),
 [forall i, Eli_dis i e@t = f (frame@t) i]

.
Proof.
   intro H.
   induction t;
      (* for all created subgoal, why try the trival proof where the state is not touched by the action. *)
      try  (destruct IH; exists (fun x => f (fst x)); expand Eli_dis,frame; rewrite H0; auto).
 
 + exists (fun x i => undef). auto.   

+ expandall. destruct IH.
  exists (fun x i0 => 
  if i = i0 && e = e0 then  LE (pid_alpha i0, r' (i', e0)) else f (fst x) i0). rewrite H0.  intro i0.  simpl ~flags:beta. fa; auto.
Qed.


global lemma public_eli0  (t:timestamp[const], e:index [const,glob]) :
  [happens(t)] -> Exists (f : message -> index -> bool_undef [adv]),
[forall i, Eli0_hon i e@t = f (frame@t) i].
Proof.
  intro H.

   induction t; 
      (* for all created subgoal, why try the trival proof where the state is not touched by the action. *)
      try  (destruct IH; exists (fun x => f (fst x)); expand Eli0_hon,frame; rewrite H0; auto).
 
 + exists (fun x i => undef). auto.   

  + destruct IH. expand frame. expand exec. expand Eli0_hon,beta.
 

   exists (fun x i0 => 
if i = i0 && e = e0 then
  if decode_bool (snd (snd (snd (att (fst x)  (* input@OLottery(i', e0, P, i0) *) )))) =
          false && f (fst x) i = undef  then
                LE (pid_alpha i0, r(i',e0))
      else  f (fst x) i (* Eli0 with H0 *)
  else  f(fst x) i0 ) (* Eli0 with H0 *)
.

 rewrite H0. intro i0. 
reduce ~flags:beta. rewrite fst_pair.   fa => //.  intro [A B] [C D]. subst e, e0. rewrite H0. auto.

Qed.

global lemma public_eli1  (t:timestamp[const], e:index [const,glob]) :
  [happens(t)] -> Exists (f : message -> index -> bool_undef [adv]),
[forall i, Eli1_hon i e@t = f(frame@t) i].
Proof.
  intro H.

   induction t; 
      (* for all created subgoal, why try the trival proof where the state is not touched by the action. *)
    try  (destruct IH; exists (fun x => f (fst x)); expand Eli1_hon,frame; rewrite H0; auto).
 
 + exists (fun x i => undef). auto.   

  + destruct IH. expand frame. expand exec. expand Eli1_hon,beta.
 

   exists (fun x i0 => 
if i = i0 && e = e0 then
  if decode_bool (snd (snd (snd (att (fst x)  (* input@OLottery(i', e0, P, i0) *) )))) =
          true && f(fst x) i = undef  then
                LE (pid_alpha i0, r(i',e0))
      else  f(fst x) i(* Eli0 with H0 *)
  else  f(fst x) i0)(* Eli0 with H0 *)
.

 rewrite H0. intro i0. 
reduce ~flags:beta. rewrite fst_pair.   fa => //.  intro [A B] [C D]. subst e, e0. rewrite H0. auto.
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


 + expand frame, exec, cond,output. fa 0; fa 1. fa 2. expand  msg,sid1. 
   have Eq : (forall (x,y:bool_undef), (x=y && diff(x,y) = dtrue) <=> (x = dtrue && y=dtrue) ).
   
  project; intro x y; split; auto.

  rewrite Eq in 1.
  expand pidi1, pidj.

  

  use public_eli0 with pred(OSend(i', e, P, i, j)), e. destruct H0.  rewrite H0.
  use public_eli1 with pred(OSend(i', e, P, i, j)), e. destruct H1. rewrite H1.

  deduce 1 => //.
  auto. auto.


 + expand frame, exec, cond,output. fa 0; fa 1.  
   have Eq : (forall (x,y:bool_undef), (x=y && diff(x,y) = dtrue) <=> (x = dtrue && y=dtrue) ).
   
  project; intro x y; split; auto.

  rewrite Eq in 1.
  expand pidi1, pidj. fa 1. 


  use public_eli0 with pred(OSend1(i', e, P, i, j)), e. destruct H0. rewrite H0.
  use public_eli1 with pred(OSend1(i', e, P, i, j)), e. destruct H1. rewrite H1.

  deduce 1 => //.
  auto. auto.

  + expandall. fa 0 => //. 

  + expandall.  

  use public_dis with pred(OLotteryCorrupted(i', e, P, i)), e. destruct H0. rewrite H0.
  fa 0 => //.  auto.

  + expandall.  

  use public_dis with pred(OLotteryCorrupted1(i', e, P, i)), e. destruct H0. rewrite !H0.
  fa 0 => //.  auto.


   
  + expandall. 

  use public_dis with pred(OSendCorrupted(i', e, P, i)), e. destruct H0. rewrite !H0.
  fa 0 => //.  auto.

  + expandall. 

  use public_dis with pred(OSendCorrupted1(i', e, P, i)), e. destruct H0. rewrite !H0.
  fa 0 => //.  auto.

 + expandall. fa 0 => //. 

 + expandall. fa 0 => //. 

 + expandall. fa 0 => //. 

 + expandall. fa 0 => //. 

Qed.


