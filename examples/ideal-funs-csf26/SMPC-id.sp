(* 

This file models the fixed SMPC ideal functionality described in our paper.

*)


(*******************************************************************)
(***            Genric function declarations                   *****)
(*******************************************************************)

include Core.
include Int.
open Int.
(* We assume that each party maps to an index, which is a builtin abstract set of elements. *) 

(* We declare an encoding function from  index to messages. *)
abstract party : index -> message.

exact axiom [any] party_inj (A, B:index) :
  (party(A) = party(B)) = (A = B).
hint rewrite party_inj.

op is_party (m:message) = exists j, m=party(j).

(* honest party *)
abstract honest_party : message -> bool.

abstract honest_P : message -> bool.


mutable beta_i ( i : index) : bool = false.

abstract empty_inputs : index -> message.
abstract empty_outputs : index -> message.

abstract bot : message.
abstract InvalidInput : message.


mutable in_i : index -> message = (fun i : index => bot).
mutable out_i : (index -> message) = (fun i : index => bot).

abstract f : (index -> message) -> (index -> message).


mutable rho : int = 0.
mutable beta : bool = false.

abstract ABORT : message.
abstract INIT : message.
abstract ALLOW : message.
mutable alpha : message =INIT. 



(* Squirrel models network communications as happening over channels, we declare a dummy one. *)
channel pub.

(* Declare a mutex to make each sub process atomic *)
mutex l : 0.


(*******************************************************************)
(***             Process/oracle declarations                   *****)
(*******************************************************************)

(* We declare for each oracle a corresponding process. *)

(* repl is the replication index, which allows to run the oracle an unbounded number of time. *)
(* index i chosen by the attacker identifies the honest party *)
process OChall(repl:index, i:index) =  
  lock l;
  in(pub, x);  (* x= (sid, P) *)
  let sid = fst(x) in
  let P = snd(x) in
  let outs = out_i in
  if P = party(i) && honest_party(P)   (* is P honest *) then
    alpha := if rho=2 && alpha = INIT then ALLOW else alpha;
    beta := (rho=2 && alpha = INIT) || (rho=2 && (fst (outs i))=ABORT && 
      (not(is_party (snd(outs i))) || (exists (j,k:index), outs j <> outs k)));
    out(pub, of_bool(beta));
    unlock l
  else
    unlock l.

process OHonesOrDisInput(repl:index, i:index) = 
  (* We merge the honest and dishonest oracles, which are perfectly equals. *)
  lock l;
  in(pub, x);  (* x=(sid, (P, x_i)) *)
  let sid = fst(x) in
  let P = fst(snd(x)) in
  let x_i = snd(snd(x)) in
  let ins = in_i in
  if P = party(i) && honest_party(P) then  (* is P honest *)
    beta_i i := if not(beta_i i) then true else beta_i i;
    in_i :=
      if not(beta_i i) then
        (fun j: index => if i=j then x_i else ins j)
      else
        in_i;
    let ins2 = in_i in
    rho := if (forall j, beta_i j ) then 2 else if not(beta_i i) then 1 else rho;     
    out_i :=
      if (forall j, beta_i j) && (forall j, ins2 j <> bot) then 
        f ins2 
      else if (forall j, beta_i j) && (exists j, ins2 j = bot)  then 
        (fun i:index => InvalidInput)		  
      else
        out_i;
    let outs  = out_i in
    out(pub, if (forall j, beta_i j) then seq(i:index => <party i, outs i>) else empty);
    unlock l
  else
    unlock l.



process OAllow(repl:index) =
  lock l;
  in(pub,x); 
  let sid = fst(x) in
  let P = snd(x) in
  alpha :=
    if not(honest_party P) && (forall j, beta_i j) && alpha = INIT then
      ALLOW
    else
      alpha;
  unlock l.


process OAbrt(repl:index) =
  lock l;
  in(pub,x); 
  let sid = fst(x) in
  let Pi = fst(snd(x)) in
  let Pj = snd(snd(x)) in
  alpha := if ((not(honest_party Pi)) && (not(honest_party Pj))
              && (forall j, beta_i j) && alpha = INIT )
           then ABORT else alpha;
  out_i := if not(honest_party Pi) && not(honest_party Pj) 
              && (forall j, beta_i j) && alpha = INIT && is_party Pj
           then (fun j:index => <ABORT, Pj >) else out_i;
  unlock l.

process OHonestOutput(repl:index, i:index) =
  lock l;
  in(pub, x);  (* x= (sid, P) *)
  let sid = fst(x) in
  let P = snd(x) in
  if P = party(i) && honest_party(P) then  (* is P honest *)
    alpha := if rho=2 && alpha = INIT then ALLOW else alpha;
    unlock l
  else
    unlock l.


abstract of_int : int -> message.

process ODisRound(repl:index) =
  lock l;
  in(pub, x);  (* x= (sid, P) *)
  let sid = fst(x) in
  let P = snd(x) in
  out(pub, if honest_party P then empty else of_int(rho));
  unlock l.

  

system ( !_i !_j OChall(i,j) 
      | !_i !_j OHonesOrDisInput(i,j) 
      |  !_i OAllow(i)
      |  !_i OAbrt(i)
      |  !_i !_j OHonestOutput(i,j)
      |  !_i ODisRound(i)
)
.


(*******************************************************************)
(***            Lemmas                                         *****)
(*******************************************************************)

axiom [any] neq_ABORT_bot : fst bot <> ABORT.

axiom [any] neq_ABORT_InvalidInput : fst InvalidInput <> ABORT.

axiom [any] neq_ABORT_f (x:index -> message,j:index) : fst (f x j) <> ABORT.

lemma abort_party : 
forall tau, happens(tau) => forall j,  
	      fst( (out_i@tau) j) = ABORT => 
	         is_party (snd( (out_i@tau) j))
	        && forall k,( (out_i@tau) k) =  (out_i@tau) j.	      
Proof.
induction.
intro tau IH Hap.
intro j.
intro Eqf.
case tau.

+ intro Eqs. rewrite /out_i /= in Eqf.  by have _ := neq_ABORT_bot. 

+ intro [i i0 Eqs].  expand out_i. by  have _ := IH (pred tau) _ _  j _=> //.

+ intro [i i0 Eqs].  expand out_i. by have _ := IH (pred tau) _ _ j _ => //.

 + intro [i i0 Eqs].  expand out_i. 
case  ((forall (j:index), beta_i j@tau) &&
             forall (j:index), (ins2@tau) j <> bot).    
       intro C.
       rewrite if_true in Eqf => //.
       by have _ := neq_ABORT_f (ins2@tau) j. 

       intro C.
       rewrite if_false in Eqf => //.
       
       case ((forall (j:index), beta_i j@tau) &&
             exists (j:index), (ins2@tau) j = bot) .  
       intro C'.
       rewrite if_true in Eqf => //.
       by have _ := neq_ABORT_InvalidInput. 

      intro C'.        
      rewrite if_false in Eqf => //.
      rewrite if_false  => //.
      rewrite if_false  => //.
      by  have _ := IH (pred tau) _ _ j _ => //.

+ intro [i i0 Eqs].  expand out_i. by have _ := IH (pred tau) _ _ j _ => //.

+ intro [i Eqs].  expand out_i. by have _ := IH (pred tau) _ _ j _ => //.

+ intro [i Eqs].  expand out_i. 
   case (not (honest_party (Pi@tau)) &&
             not (honest_party (Pj@tau)) &&
             (forall (j:index), beta_i j@pred tau) && alpha@tau = INIT  && is_party (Pj@tau)) .
   intro C. 
   rewrite if_true => //.


   intro C.
   rewrite if_false in Eqf => //.
   rewrite if_false => //.
   by have _ := IH (pred tau) _ _ j _  => //.

+ intro [i i0 Eqs].  expand out_i. by have _ := IH (pred tau) _ _  j _=> //.


+ intro [i i0 Eqs].  expand out_i. by have _ := IH (pred tau) _ _ j _ => //.

+ intro [i Eqs].  expand out_i. by have _ := IH (pred tau) _ _ j _ => //.
Qed.



axiom [any] neq_ALLOW_INIT : ALLOW <> INIT.



(*******************************************************************)
(***            Security Theorem                               *****)
(*******************************************************************)

lemma not_beta (tau:timestamp):
   happens(tau) => not(beta@tau).
Proof.
induction tau.
intro tau IH Hap.
case tau;

try  ((intro [i Eqs];  expand beta; by have _ := IH (pred tau)  => //)
	    +
 (intro [i j Eqs];  expand beta; by have _ := IH (pred tau)  => //)

	    )
.


auto.

intro [i i0 Ts].
rewrite /beta.
rewrite not_or.
split.
 +  rewrite not_and.
    rewrite -impl_charac.
    intro Rho.
    rewrite /alpha.
    rewrite Rho. 
    case  alpha@pred tau = INIT.

    ++ intro C. simpl. by apply neq_ALLOW_INIT.
    ++ auto.

 + rewrite not_and -impl_charac not_and -impl_charac not_or /=.
   intro Rho Eq.
   have A := abort_party tau _ i0 _ => //. 
   split. auto. rewrite not_exists_2. intro a b. simpl.
   destruct A as [_ A].  
   rewrite /outs.
   have Aa := A a.  
   rewrite /out_i in Aa.
   rewrite Aa.

   have Ab := A b.  
   rewrite /out_i in Ab.
   by rewrite Ab.
Qed.  
