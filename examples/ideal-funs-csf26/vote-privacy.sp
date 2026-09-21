(* This file models the ideal functionality from [A].

It  proves that the ideal functionality  verifies vote privacy. 

[A]: A. Szepieniec and B. Preneel, “New techniques for electronic voting,”
USENIX Journal of Election Technology and Systems (JETS), Aug. 2015

*)

(*******************************************************************)
(***            Genric function declarations                   *****)
(*******************************************************************)

include Core.

(* We assume that each honest voter maps to an index, which is a builtin abstract set of elements. *) 

(* We declare an encoding function from  index to messages. *)
abstract voter : index -> message.

exact axiom [any] voter_inj (A, B:index) :
  (voter(A) = voter(B)) = (A = B).
hint rewrite voter_inj.

(* Global state for the tallied value. *)
mutable tallied : bool = false.

(* Squirrel models network communications as happening over channels, we declare a dummy one. *)
channel pub.

(* We define the honest voter function. *)
abstract honest_voter : message -> bool.
axiom [any] honest_voter_def (x:message):
   honest_voter(x) = exists i:index, x=voter(i).


(* Chainedlist functions for the game experiment*)
type chainedlist [serializable].

abstract nill:chainedlist.
mutable vote0 : chainedlist = nill.
mutable vote1 : chainedlist = nill.
abstract (&+) : chainedlist -> chainedlist -> chainedlist.  (* concat operator *)
axiom [any] empty_conc (u:chainedlist) :
  nill &+ u = u.
abstract Ballot : message * message -> chainedlist.   (* element constructor Ballot(voter,vote) *)



abstract is_in : chainedlist * chainedlist -> bool.


axiom [any] empty_chain (u,v:message):
  is_in(Ballot(u,v),nill) = false.

axiom [any] is_in_rec (u,v,u',v':message, x :chainedlist):
  is_in(Ballot(u,v),x &+ Ballot(u',v')) = ( (u=u' && v=v') || is_in(Ballot(u,v),x)).


axiom [any] assoc_conc (x,y,z:chainedlist):
  (x &+y) &+ z = x &+ y &+ z.


(* Ideal functionality defs *)

abstract rho : chainedlist * chainedlist -> message.

mutable ballotbox : chainedlist = nill.

(* ghost variables for bookkeeping *)

mutable ballotbox_hon : chainedlist = nill.
mutable ballotbox_dis : chainedlist = nill.

abstract tally : chainedlist * chainedlist -> message.

mutable noblocks : chainedlist=nill.

abstract Noblock : message -> chainedlist.


(* Given three chainedlist prefix, x and y that all contain votes of
the form Ballot(agent,vote_value), if there is no vote in x and y that
pertain to the same agent, then the order in which we add x or y to
the prefix does not change the ideal rho counting result. *)
axiom [any] comm_conc (prefix,x,y,bl:chainedlist):
  (forall (u,v,u',v':message),
   is_in(Ballot(u,v),x) && is_in(Ballot(u',v'),y) => u <> u') =>
  rho(prefix &+ x &+ y,bl) = rho (prefix &+ y &+ x,bl).

axiom [any] extendable_rho (x,y,z,bl:chainedlist) :
  rho(x,bl) = rho(y,bl) => rho(x &+ z,bl) = rho(y &+ z,bl).


axiom [any] correct_tally (x,y,bl:chainedlist) :
  (rho(x,bl) = rho(y,bl)) =>  tally(x,bl)=tally(y,bl).

(* Declare a mutex to make each sub-process atomic *)
mutex l : 0.

(*******************************************************************)
(***             Process/oracle declarations                   *****)
(*******************************************************************)


(* We declare for each oracle a corresponding process. *)

(* repl is the replication index, which allows to run the oracle an unbounded number of time. *)
process Ovote(repl:index, i:index) =
  lock l;
  in(pub, x);  (* x= (sid, (V, (vi,vj))) *)
  let sid = fst(x) in
  let V = fst(snd(x)) in
  let vi = fst(snd(snd(x))) in
  let vj = snd(snd(snd(x))) in
  if V = voter(i) && not(tallied) then
    (* is voter honest and we did not tallied? *)
    vote0 := vote0 &+ Ballot(V,vi);
    vote1 := vote1 &+ Ballot(V,vj);
    (* Begin Send(vote,sid,v) to Pi from V *)
    ballotbox := ballotbox &+ Ballot(V,diff(vi,vj)); 
    (* for bookeeping *)
    ballotbox_hon := ballotbox_hon &+ Ballot(V,diff(vi,vj));
    (* end bookkeeping *)
    out(pub, <sid,V>);
    (* End Send(vote,sid,v) to Pi from V *)
    unlock l
  else
    unlock l.

process OvoteCorrupted(repl:index) =
  lock l;
  in(pub, x);  (* x=(sid, (V, v)) *)
  let sid = fst(x) in
  let V = fst(snd(x)) in
  let v = snd(snd(x)) in
  if exists i, V = voter(i) || tallied then  
    unlock l
  else
    (* is voter dishonest and we did not tally? *)
    ballotbox := ballotbox &+ Ballot(V,v); 
    (* for bookeeping *)
    ballotbox_dis := ballotbox_dis &+ Ballot(V,v);
    unlock l.

process NoBlocs(i:index) = 
  lock l;
  in(pub,x);
  noblocks :=   noblocks &+ Noblock(x);
  unlock l.

process Otally =
  lock l;
  in(pub,sid); 
  if rho(vote0, noblocks) = rho(vote1, noblocks) then
    tallied := true;
    (* Begin Send (tally,sid) to Pi *)
    out(pub,tally(ballotbox, noblocks));
    (* End Send (tally,sid) to Pi *)
    unlock l
  else
    unlock l.


system (Otally | !_i NoBlocs(i) | !_i !_j Ovote(i,j) | !_i OvoteCorrupted(i) ).

(*******************************************************************)
(***            Lemmas                                         *****)
(*******************************************************************)

global lemma bb_hon  (t:timestamp[const]) :
  [happens(t)] -> [forall (V,u:message), (exec@t => (is_in(Ballot(V,u), ballotbox_hon@t) => honest_voter(V)))].
Proof.
  induction t => Hap.
  + expandall. rewrite empty_chain. auto.
  + expandall. intro E u. have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //. 
  + intro E V u C.  expand ballotbox_hon. rewrite is_in_rec in C.  case C.
    ++ expand exec,cond. rewrite honest_voter_def. exists j.  auto. 
    ++  have H  := IH _ E V => //.  

  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
Qed.

global lemma vote0_hon  (t:timestamp[const]) :
  [happens(t)] -> [forall (V,u:message), (exec@t => (is_in(Ballot(V,u), vote0@t) => honest_voter(V)))].
Proof.
  induction t => Hap.
  + expandall. rewrite empty_chain. auto.
  + expandall. intro E u. have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + intro E V u C.  expand vote0. rewrite is_in_rec in C.  case C.
    ++ expand exec,cond. rewrite honest_voter_def. exists j.  auto. 
    ++  have H  := IH _ E V => //.  

  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
Qed.



global lemma bb_dis  (t:timestamp[const]) :
  [happens(t)] -> [forall (V,u:message), (exec@t => (is_in(Ballot(V,u), ballotbox_dis@t) => not(honest_voter(V))))].
Proof.
  induction t => Hap.
  + expandall. rewrite empty_chain. auto.
  + expandall. intro E u. have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + expandall. intro E u.  have H' := IH _ E u=> //.   
  + intro E V u C.  expand ballotbox_dis. rewrite is_in_rec in C.  case C.
    ++ expand exec,cond. destruct u.

 rewrite honest_voter_def. 
rewrite  not_exists_1.
simpl.
intro a Eq.
rewrite  not_exists_1 in H0.
have L := H0 a.
auto. 

    ++  have H  := IH _ E V => //.  
Qed.


global lemma bb_split_rho'  (t,t':timestamp[const]) :
  [happens(t,t')] -> [exec@t => 
rho(ballotbox@t, noblocks@t') = rho(ballotbox_hon@t &+ ballotbox_dis@t, noblocks@t')
].
Proof.
  induction t => Hap.
  + expandall. rewrite empty_conc => //.
  + expandall. intro E. rewrite IH => //.
  + expandall. intro E. rewrite IH => //.
  + expandall. intro E. rewrite IH => //.
  + expand ballotbox, ballotbox_dis,ballotbox_hon. intro E. 
   have IH' := IH _ => //. 
   localize IH' as C. have C' := C _ => //.


   have Eq :=  (extendable_rho  (ballotbox@pred (Ovote(i, j)))
  (ballotbox_hon@pred (Ovote(i, j)) &+ ballotbox_dis@pred (Ovote(i, j)))
  (Ballot (V@Ovote(i, j), diff(vi@Ovote(i, j), vj@Ovote(i, j))))
)    (noblocks@t')  _ => //. 
   
   rewrite assoc_conc.
   have Rw := comm_conc (ballotbox_hon@pred (Ovote(i, j))).
  

   rewrite  Rw.

   intro u v1 u' v2 [I1 I2] L.
   subst u',u.   
 

   rewrite -(empty_conc   (Ballot (V@Ovote(i, j), diff(vi@Ovote(i, j), vj@Ovote(i, j))))) in I1.

   rewrite is_in_rec in I1.
   case I1.
   subst u, V@Ovote(i,j).



  expand exec,cond.  destruct E as [G T].  


   have H := bb_dis (pred (Ovote(i,j))) _ (V@Ovote(i,j)) (v2)  => // .
  localize H as H'.
   have H0 := H' _ _  => //.
  rewrite honest_voter_def in H0.    

   rewrite not_exists_1 in H0. simpl.
   by have _ := H0 j.
  

  
  by  rewrite empty_chain in I1.


 rewrite assoc_conc in Eq. auto.






 + expandall. intro E. rewrite IH => //.
 + expandall. intro E. rewrite IH => //.

  + expand ballotbox, ballotbox_dis,ballotbox_hon. intro E. 
   have IH' := IH _ => //. 
   localize IH' as C. have C' := C _ => //.


   have Eq :=  (extendable_rho (ballotbox@pred (OvoteCorrupted1(i)))
  (ballotbox_hon@pred (OvoteCorrupted1(i)) &+  ballotbox_dis@pred (OvoteCorrupted1(i)))
   (Ballot (V1@OvoteCorrupted1(i), v@OvoteCorrupted1(i)))
) (   noblocks@t') _ => //. 

  by rewrite assoc_conc in Eq.
Qed.

global lemma bb_split' (t:timestamp[const]) :
  [happens(t)] -> [exec@t => 
tally(ballotbox@t,    noblocks@t) = tally(ballotbox_hon@t &+ ballotbox_dis@t,    noblocks@t)
].
Proof.
  intro Hap. intro Ex.
  have C := correct_tally (ballotbox@t)  (ballotbox_hon@t &+ ballotbox_dis@t) (   noblocks@t)_ => //.

  have D := bb_split_rho' t t _ => //.
Qed.


(* Basic lemma to show that the attacker always knows the voting sets *)
global lemma public_vote0  (t:timestamp[const]) :
  [happens(t)] -> Exists (f : message -> chainedlist [adv]), [vote0@t = f(frame@t)].
Proof.
intro H.
induction t.
    + exists (fun x:message => nill); auto.
 + destruct IH; expand vote0, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand vote0, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand vote0, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand vote0, frame.   
   expand V,vi,input.   
   exists (fun x:message => 
f(fst x ) &+
   Ballot
     (fst (snd (att (fst x ))),
      fst (snd (snd (att (fst x )))))) => //.
 + destruct IH; expand vote0, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand vote0, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand vote0, frame.   
   exists (fun x:message => f (fst x)) => //.
Qed.   

(* Basic lemma to show that the attacker always knows the voting sets *)
global lemma public_vote1  (t:timestamp[const]) :
  [happens(t)] -> Exists (f : message -> chainedlist [adv]), [vote1@t = f(frame@t)].
Proof.
intro H.
induction t.
    + exists (fun x:message => nill); auto.
 + destruct IH; expand vote1, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand vote1, frame.   
   exists (fun x:message => f (fst x)) => //
 + destruct IH; expand vote1, frame.   
 + destruct IH; expand vote1, frame.   
     exists (fun x:message => f (fst x)) => //
 + destruct IH; expand vote1, frame.   
 + destruct IH; expand vote1, frame.   
   expand V,vj,input.   
   exists (fun x:message => 
f(fst x ) &+
   Ballot
     (fst (snd (att (fst x ))),
      snd (snd (snd (att (fst x )))))) => //.
 + destruct IH; expand vote1, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand vote1, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand vote1, frame.   
   exists (fun x:message => f (fst x)) => //.
Qed.   

global lemma public_bb_dis  (t:timestamp[const]) :
  [happens(t)] -> Exists (f : message -> chainedlist [adv]), [ballotbox_dis@t = f(frame@t)].
Proof.
intro H.
induction t.
    + exists (fun x:message => nill); auto.
 + destruct IH; expand ballotbox_dis, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand ballotbox_dis, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand ballotbox_dis, frame.   
   exists (fun x:message => f (fst x)) => //.

 + destruct IH; expand ballotbox_dis, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand ballotbox_dis, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand ballotbox_dis, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand ballotbox_dis, frame.   
   exists (fun x:message => 
f(fst x ) &+
   Ballot
     (fst (snd (att (fst x ))),
      snd (snd (att (fst x ))))) => //.
Qed.   


global lemma public_noblocks  (t:timestamp[const]) :
  [happens(t)] -> Exists (f : message -> chainedlist [adv]), [noblocks@t = f(frame@t)].
Proof.
intro H.
induction t.
    + exists (fun x:message => nill); auto.
 + destruct IH; expand noblocks, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand noblocks, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand noblocks, frame.   
   exists (fun x:message => 
f(fst x ) &+
   Noblock
     ((att (fst x )))) => //.

 + destruct IH; expand noblocks, frame.   
   exists (fun x:message => f (fst x)) => //.

 + destruct IH; expand noblocks, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand noblocks, frame.   
   exists (fun x:message => f (fst x)) => //.
 + destruct IH; expand noblocks, frame.   
   exists (fun x:message => f (fst x)) => //.

Qed.   


(* Basic lemma to show that the attacker always knows the tallied status *)
global lemma tallied_case (t:timestamp[const]) :
  [happens(t)] -> [tallied@t=true] \/  [tallied@t=false].
Proof. 
   intro H.

  induction t.  

   expandall; right; auto.


   expandall;left; auto.

   expandall; auto.

   expandall; auto.
   expandall; auto.
   expandall; auto.
   expandall; auto.
   expandall; auto.
Qed.  

(* Basic lemma to show that the ballox box is always the diff of both ideal voting sides. *)
global lemma bb_is_diff_vote (t:timestamp[const]) :
  [happens(t)] -> [ballotbox_hon@t = diff(vote0@t,vote1@t)].
Proof. 
induction t => H.
 + expandall. project; auto. 
 + expandall. apply IH. auto.
 +  expandall. apply IH. auto.
 +  expandall.  use IH. auto. auto.
 +  expandall.  use IH.
    project; auto. 
    auto.
 +  expandall. apply IH. auto.
 +  expandall. apply IH. auto.
 +  expandall. apply IH. auto.
Qed.  

lemma secure (t:timestamp[const]) :
happens(t) 
=> rho (vote1@t, noblocks@t) =  rho (vote0@t, noblocks@t)
=>
tally (vote1@t &+ ballotbox_dis@t, noblocks@t) = tally (vote0@t &+ ballotbox_dis@t, noblocks@t).
Proof. 
intro H Eq.
have Rw :=  (extendable_rho  (vote1@t)  (vote0@t)  (ballotbox_dis@t)) (noblocks@t) _ => //.


have C :=    correct_tally  (vote1@t &+ ballotbox_dis@t) (vote0@t &+ ballotbox_dis@t) (noblocks@t) _ => //. 
Qed.

(*******************************************************************)
(***            Security Theorem                               *****)
(*******************************************************************)

(* The final indistinguishability goal, where `equiv` directly asks to
prove that the given system is diff-equivalent. *) 
equiv voteprivacy.
Proof.
  induction t.
  
  +  auto.

   (* hardest case : is the tally diff equivalent ? *)  
  + expand frame,output. 



    have Split := bb_split' Otally.



   expand exec,cond, ballotbox_hon,ballotbox_dis. 
   fa 0; fa 1.

   rewrite /noblocks /ballotbox in Split.
   rewrite Split => // {Split}.



    (* we replace the bb with the diff of the votes *)
  use bb_is_diff_vote with pred Otally.

    rewrite H0.

    (* we now add the hypothesis that the diff is useless as the condition implies equality. *)
   have Eq : 
 (if (exec@pred Otally && rho (vote0@pred Otally, noblocks@pred Otally) = rho (vote1@pred Otally, noblocks@pred Otally))
     then tally ( diff(vote0@pred Otally, vote1@pred Otally) &+ ballotbox_dis@pred Otally, noblocks@Otally)) =
 (if (exec@pred Otally && rho (vote0@pred Otally, noblocks@pred Otally) = rho (vote1@pred Otally, noblocks@pred Otally))

     then tally (vote0@pred Otally &+ ballotbox_dis@pred Otally, noblocks@pred Otally)).
     (* we prove this hypothesis *)
     project. fa; auto. 



     have C := secure (pred Otally) _  => //.  expand  noblocks@Otally.
     rewrite C => //.
  rewrite /noblocks in Eq.
   rewrite Eq.
   
  (* We used the hypothesis, so now there are no more diff. *)
  (* We only need to show that the attacker learns nothing new that it could not compute before. *)

    use public_vote0 with pred(Otally).
    destruct H1.
    rewrite H1.
    use public_vote1 with pred(Otally).
    destruct H2.
    rewrite H2.
    use public_bb_dis with pred(Otally).
    destruct H3.
    rewrite H3.
    use public_noblocks with pred(Otally).
    destruct H4.
    rewrite H4.
    deduce => //.
    auto.
    auto.
    auto.
    auto.   
    auto.
  (* For all remaining cases, we also only need to show that the attacker learns nothing new that it could not compute before. *)

  + expand frame,output,exec,cond; fa 0; fa 1.  
    use public_vote0 with pred(Otally1).
    destruct H0.
    rewrite H0.
    use public_vote1 with pred(Otally1).
    destruct H1.
    rewrite H1.
    use public_noblocks with pred(Otally1).
    destruct H2.
    rewrite H2.
    auto.
    auto.
    auto.
    auto.


  + expand frame,output,exec,cond; fa 0. 

    have H1 := tallied_case (pred (NoBlocs(i))).
    use H1.
    case H0.

    auto. auto. auto.


  + expand frame,output,exec,cond; fa 0; fa 1.  

    have H1 := tallied_case (pred (Ovote(i, j))).
    use H1.
    case H0.
    ++ expand V,sid; rewrite H0;  auto.
    ++ expand V,sid; rewrite H0;  auto.
    auto.


   + expand frame,output,exec,cond; fa 0; fa 1.  

    expand V.
    have H1 := tallied_case (pred (Ovote1(i,j))).
    use H1.
    case H0.
    ++ rewrite H0; auto.
    ++ rewrite H0; auto.
    auto.

   + expand frame,output,exec,cond,V1; fa 0; fa 1.  
    have H1 := tallied_case (pred (OvoteCorrupted(i))).
    use H1. case H0.
    ++ rewrite H0; auto.
    ++ rewrite H0; auto.
    auto.


   + expand frame,output,exec,cond,V1; fa 0; fa 1. 
    have H1 := tallied_case (pred (OvoteCorrupted1(i))).
    use H1. case H0.
    ++ rewrite H0; auto.
    ++ rewrite H0; auto.
    auto.

Qed.
