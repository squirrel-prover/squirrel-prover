(* This file models a very basic hash chain.
   A Random Oracle is modelled using a hash function `h` 
   with a secret key `k`. 
   A state `ck` stores the ratchetting chain-key. 
   It is initialized to some secret value `s`. 
   Then, agent `A` on input `x`, updates state `ck` to `h(<ck,x>,k)`.
   We allow the attacker to corrupt at some point `ck`, 
   and prove that all previous state values are secret. *)

(*------------------------------------------------------------------*)
include Core.
include NonDeduction.

(*------------------------------------------------------------------*)
(* The public communication channel. *)
channel c.

(*------------------------------------------------------------------*)
(* The random oracle hash function. *)
hash h.
name k : message.

(*------------------------------------------------------------------*)
(* We initialize a state to a secret value. *)
name s : message
mutable ck : message = s.

(*------------------------------------------------------------------*)
(* Dummy output sent over the network. *)
op ok:message.

(*------------------------------------------------------------------*)
(* Both the honest and the corrupted agents have access to `ck`. 
   This mutex guarantees that no data-races occur on `ck`. *)
mutex l : 0.

(*------------------------------------------------------------------*)
(* Code for the agent `A`. *)
process A (i : index) = 
  lock l;
  in(c, x);

  (* update the state and returns ok *)
  ck := h(<ck,x>,k);

  out(c, ok); 
  unlock l.

(*------------------------------------------------------------------*)
(* A corrupted variant of `A`, which updates its state and 
   then leaks its. *)
process Corrupt = 
  lock l;
  in(c,u);

  ck := h(<ck,u>,k);

  out(c, ck);
  unlock l.

(*------------------------------------------------------------------*)
(* The ROM, allowing the attacker to compute hashes. *)
process ROM (j:index) =
  in(c,x);
  out(c, h(x,k)).

(*------------------------------------------------------------------*)
(* We put all parties in parallel, and allow `A` and the `ROM` to be
   called any number of times. Since we only consider forward secrecy,
   there is no reason to allow multiple corruptions (once `A` is
   corrupted, security cannot be recovered). *)
system S = (!_i A i) | (!_j ROM j) | Corrupt.


(*------------------------------------------------------------------*)
(* The predicate `safe t` states whether `ck@t` is safe, i.e. 
   cannot be computed by the attacker.
   For this protocol, we only need that `Corrupt` did not 
   occur before `t` *)
let safe @system:S (t : timestamp) = 
  forall t', t' <= t => t' <> Corrupt.

(*------------------------------------------------------------------*)
(* We describe the high-level structure of the proof.

  We want to prove the forward secrecy of safe states, i.e.
   `Forall t t', [happens(t,t')] -> [safe t] -> $( (frame@t') *> (ck@t))`.
   
  We split this proof in several steps:
  - 1. Non-Collision: we prove a number of non-collision properties.
  - 2. Simulation: we define a set of oracles that can simulate `frame@t'`.
  - 3. Secrecy: we show that `ck@t` cannot be deduced from those oracles.
*)

(*------------------------------------------------------------------*)
(* Step 1. Non-Collision *)

(*------------------------------------------------------------------*)
(* We use pre-image resistance to show that all values of the state in
   the hash-chain are different from the initial seed `s`. *)

(* The preimage resistance assumption *)
game PIR = {
  rnd k:message;

  (* First, the adversary choses a value `goal` without
     using the oracles. *)
  let goal : message = #init;

  (* Then, it can computes as many hashes as it wants. *)
  oracle get_h x = { return h(x,k) }

  (* Or obtain back the value of `goal`. *)
  oracle get_goal = { return goal }

  (* With overwhelming probability, the adversary cannot produce a
     pre-image `x` of `goal`, i.e. a value `x` such that `h(x,k) =
     goal`. *)
  oracle challenge x = { return diff(h(x,k) <> goal, true) }
}.

(*------------------------------------------------------------------*)
(* There is no collision between a non-initial element of the
   hash-chain and the initial element of the hash-chain (thanks to
   pre-image resistance). *)
lemma [set:S/left; equiv:S/left,S/left] NoCollisionInit (i:index):
  happens(A i) => ck@(A i) <> s.
Proof.
  intro Hap.
  rewrite /ck.
  ghave H : equiv(diff(h (<ck@pred (A(i)),input@A(i)>, k) <> s, 
                  true)).
  { crypto PIR (goal:s) (k:k). }.
  by rewrite equiv H.
Qed.

(*------------------------------------------------------------------*)
(* Functional property of the state `ck@t`, showing that scheduled and
   safe `t` are such that:
   - either `ck@t = s` 
   - or `ck@t = ck@ A j`, for some `j` such that `A j < t` and
     no `A` action occurred between `A j` and `t` *)
lemma pred_A @set:S/left (t:timestamp):
  happens(t) => 
  safe t =>
  ( (ck@t = s && not (exists l, A l <= t))
    ||
    (exists j, 
       ck@t = ck@A j && 
       A j <= t && 
       not (exists l, A j < A l && A l <= t))).
Proof.
  induction t.
  intro t IH Hap safe.
  case t. 
  
  + intro Eq.
    by left.
  + intro [i Eq].
    right. exists i. auto.
  + intro [i Eq].
    have I // := IH (pred t) _ _ _; 1: smt.
    case I; smt.
  + intro Eq.
    have I // := IH (pred t) _ _ _.
    smt.
Qed.

(*------------------------------------------------------------------*)
(* There is no collision between two distinct 
   non-initial safe elements of the hash-chain. *)
lemma NoCollisionA_aux @set:S/left (tau', tau : timestamp):
  tau < tau' => 
  safe tau' => 
  (exists i, tau = A i) => (exists j, tau' = A j) => 
  ck@tau <> ck@tau'. 
Proof.
  generalize tau'.
  induction tau.
  intro tau' IH tau I S [i H1] [j H2] F.
  rewrite H1 H2 in *.
  clear H1 H2 tau tau'.
  rewrite /ck in F.
  collision => {F} F.
  apply (f_apply fst) in F.
  rewrite /= in F.
    
  have pAj // := pred_A (pred (A j)) _ _; 1:smt.
  case pAj; 1:smt. 
  destruct pAj as [j0 [E1 E2]]. 

  have pAi // := pred_A (pred (A i)) _ _; 1:smt.
  case pAi. 
  + destruct pAi as [E3 E4].
    rewrite E3 E1 in F.
    by have T := NoCollisionInit j0 _ => //.  

  + destruct pAi as [i0 [E3 E4]].
    rewrite E3 E1 in F.
    have IF := IH (A j0) (A i0) _ _ _; smt. 
Qed.

lemma NoCollisionA @set:S/left (i, j : index):
  A i < A j => 
  safe (A j) => 
  ck@(A i) <> ck@(A j). 
Proof.
  intro ??.
  apply NoCollisionA_aux => //. 
  by exists i.
  by exists j.
Qed.

(*------------------------------------------------------------------*)
(* Step 2. Simulation *)

(*------------------------------------------------------------------*)
(* We define our oracles. *)

(* A ROM oracle. *)
let Oh = fun x => h(x,k).

(* An oracle giving the corrupted value `ck@Corrupt`. *)
let C @system:S = if happens(Corrupt) then ck@Corrupt.

let leakage @system:S = (Oh,C).

(*------------------------------------------------------------------*)
(* These oracles are enough to simulate the frame. *)
global lemma simulate_frame @set:S/left (t:timestamp [const]):
  [happens(t)] -> $( leakage |> (frame@t)).
Proof.
  intro H.
  induction t.
  
   + deduce.
   + rewrite /frame. apply IH.
   + rewrite /frame.
     fa !<_,_>. fa 2.
     deduce with IH.
     rewrite /output. 
  
     rewrite /(|>) in *. 
     destruct IH as [get_frame Eq].
  
     rewrite /input.
     exists (fun x : _ * _ => (x#1) ( att( get_frame (x#1,x#2)))). 
     localize Eq as _; auto. 

   + rewrite /frame /leakage /C /output.
     by deduce with IH.
Qed.

(*------------------------------------------------------------------*)
(* Further, if there was no compromise, `Oh` is sufficient. *)
global lemma simulate_safe_frame @set:S/left (t:timestamp [const]):
  [happens(t)] -> [safe t] -> $( Oh |> (frame@t)).
Proof.
  intro H S.
  induction t.
  
   + deduce.
   + rewrite /frame. apply IH. smt. 
   + rewrite /frame.
     fa !<_,_>. fa 2.
     have Sp : safe (pred (ROM j)); 1: smt.
     deduce with IH. { assumption. }.
     rewrite /output. 
  
     rewrite /(|>) in *. 
     have IH2 := IH Sp => {IH}. 
     destruct IH2 as [get_frame Eq].
  
     rewrite /input.
  
     by exists (fun x : _  => (x) ( att( get_frame (x)))). 
  
   + rewrite /safe in S. 
     have neg /= := (S Corrupt) _; 1: auto. 
     constraints. 
Qed.


(*------------------------------------------------------------------*)
(* Step 3. Secrecy
  
   We now prove the secrecy of `ck@t` when `safe t` from the
   inputs `(Oh,C)`. *)

(*------------------------------------------------------------------*)
(* if `t` is safe, then any earlier `t'` is safe *)
lemma earlier_safe @system:S/left (t, t' : timestamp) :
  t' <= t => safe t => safe t'.
Proof. smt. Qed.


(*------------------------------------------------------------------*)
(* First notice that if `t` is safe and only with access to `Oh`, 
   this is trivial, as the chain depends on a secret occuring 
   nowhere else. *)
global lemma base_secrecy @set:S/left (t:timestamp[const]):
   [happens(t)] -> [safe(t)] -> $( Oh *> (ck@t)).
Proof.
  intro H S. 
  induction t.
  + rewrite /ck. 
    by fresh.
  + rewrite /ck.
    rewrite /Oh.
    prf ~right ~under_hash 0. {
      repeat split.
      - intro j HRO Heq.
        (* impossible, as `ck@pred (A i)` is secret by `IH` *)
        apply f_apply fst in Heq; simpl.
        have DF := simulate_safe_frame (pred (ROM j)) _ _; 
          [1:by apply earlier_safe (A i) | 2: by constraints].
        rewrite /( |> ) in DF.
        destruct DF as [f HF].
        rewrite /input -HF in Heq; clear HF.
        have IH' := IH _ ; [1:by apply earlier_safe (A i)]; clear IH.
        rewrite /( *> ) in IH'.
        by have _ := IH' (fun (o:message -> message) => fst (att (f o))).
      - intro i0 O. 
       (* impossible as there are no collision between 
          safe distinct points in the hash-chain *)
        have A := NoCollisionA i0 i O _; 1:auto.
        clear IH H S. 
        smt.
      - smt. (* contradiction between `Corrupt < A i` and `safe (A i)` *)
    }.
    apply IH. 
    by apply earlier_safe (A i).
  + rewrite /ck. 
    apply IH.
    by apply earlier_safe (ROM j).
  + (* impossible, since we assumed there is no corruption *)
    rewrite /safe in S.
    have _ := S Corrupt _; by constraints.
Qed.


(*------------------------------------------------------------------*)
(* With `C` on the left-hand side, it is more complex. 

  The idea is to use `prf` to eliminate `C` from the 
  LHS of `$( (Oh, C ) *> (ck@t) )`.

  When doing so, we need that the value hashed `C` has not been
  hashed anywhere else. But we now see that `ck@t` occurs in `C`, and
  that `C` might collide with past hashes, which we deal with using 
  our non-collision lemmas. *)    

(*------------------------------------------------------------------*)
(* Utility lemma capturing a secrecy rule. *)
global lemma
  no_ded_ded @set:S/left ['a 'b 'c]  (u : 'a) (v : 'b) (w : 'c) : 
    $(u *> w) ->
    $(u |> v) ->
    $(v *> w).
Proof.
   intro @/( |> ) @/( *> ) H1 [f H2] g.
   have A /= := H1 (fun x => g(f x)).
  auto.
Qed.

lemma simpl_or_right @system:any b1 b2 : (b2 => b1) => (b1 || b2) = b1.
Proof. smt. Qed.

(*------------------------------------------------------------------*)
(* The main proof of secrecy. *)
global lemma secrecy @set:S/left (t:timestamp [const]):
  [happens(t)] -> 
  [safe t] ->
  $( leakage *> (ck@t) ).
Proof.
  intro H Safe.

 (* We first easily deal with the case where no corruption
    happen using `base_secrecy` *)
  ghave [C|C] : [not(happens(Corrupt)) || 
                 (happens(Corrupt))] 
  by constraints. {
    rewrite /leakage /C if_false //.  
    deduce. 
    by apply base_secrecy.
  }.
  
  (* We must show that `$((Oh , ck@Corrupt) *> ck@t)` *)

  have Ord0 : t < Corrupt; 1:smt.

  rewrite /leakage /C if_true //.
  rewrite /ck /Oh.
  set v @system:S/left := <ck@pred Corrupt,input@Corrupt>.

  (* Simplify and expose the oracles. We have that:
     `ck@Corrupt = h (v, k))` 
     where `v := <ck@pred Corrupt, input@Corrupt>` *)

  (* We apply `prf` on the corrupted hash from `C`.
     We must prove that:
     - A. `v` has never been hashed in the time interval `[init; Corrupt[`, i.e.:
       + Collision 1: `∀ ROM j < Corrupt,  v ≠ input@ROM j)`
          ⇒ `ck@pred Corrupt` is secret by `base_secrecy` (as 
             `pred Corrupt` is safe), which is in contradiction
              with the fact that `v := <ck@pred Corrupt, ...>`
       + Collision 2: `∀ Corrupt < Corrupt,  v ≠ <ck@pred Corrupt,input@Corrupt>`
          ⇒ trivially, `Corrupt < Corrupt ⇒ ⊥`
       + Collision 3: `∀ A i < Corrupt,  v ≠ <ck@pred (A i),input@A(i)>`
          ⇒ `v := <ck@pred Corrupt, ...>`, and `ck@pred Corrupt` cannot 
             be equal to `ck@pred (A i)` since both values of the state
             correspond to different safe points in the hash-chain
             (indeed, `pred(A i) < A i < pred Corrupt`)
     - B. `$(Oh *> v)`   , i.e. `v`    cannot be computed from `Oh`
       ⇒ consequence of `base_secrecy`
     - C. `$(Oh *> ck@t)`, i.e. `ck@t` cannot be computed from `Oh`
       ⇒ consequence of `base_secrecy`
   *) 
  prf ~left ~under_hash 1.
 
  (* A. We prove that `v` hash never been hashed *)
  + split; 2:split.

   (* Case 1: `∀ ROM(j) < Corrupt t,  v ≠ input@ROM(j))` *)
   - intro j Ord Collision. 
     (* `v` cannot have been sent to a past call to the `ROM`,
         because part of `v` (`ck@pred Corrupt`) is secret 
         under `Oh`. *)

     (* since `t` is safe, it occurs before `Corrupt`, which 
        allows to simplify the scenario *)
     rewrite simpl_or_right in Ord; 1:auto.
 
     (* before the `ROM` call, we are safe, so we just 
        need `Oh` to simulate it *)
     have DedF // := simulate_safe_frame (pred (ROM j)) _ _. 

     (* `pred Corrupt` is before the corruption and 
        thus safe, so we use base secrecy. *)
     have NDedf := base_secrecy (pred Corrupt) _ _; 1,2: auto.
 
     apply (no_ded_ded _ _ _ NDedf) in DedF => {NDedf}. 
     (* thus, we know that `$(frame@pred (ROM j) *> ck@pred Corrupt)` *)

     (* which contradict the collision `v = input@ROM j` 
        (since `v := <ck@pred Corrupt, ...>`) *)
     rewrite /( *> ) in DedF.
     by have _ := DedF (fun x => fst (att x)).
 
   (* Collision 2: `∀ Corrupt < Corrupt: v ≠ <ck@pred Corrupt,input@Corrupt>`
      Immediate contradiction in `Corrupt < Corrupt` *)
   - smt.

   (* Collision 3: `∀ A(i) < t, v ≠ <ck@pred (A i),input@A i>` *)
   - intro i Ord Collision. 
     (* maybe `v` collides with a past hash at done in `ck@A i` *)

     (* since `t` is safe, it occurs before `Corrupt`, which 
        allows to simplify the scenario *)
     rewrite simpl_or_right in Ord; 1:auto.

     apply (f_apply fst) in Collision.
     rewrite /v /= in Collision.
     (* we know that we have the collision
        `ck@pred Corrupt = ck@pred (A i)` *)

     (* `pred Corrupt` is safe *)
     have Sc : safe (pred Corrupt); 1:smt. 
 
     (* we find the `A j` such that `ck@(pred Corrupt) = ck@A j` *)
     have pC := pred_A (pred Corrupt) _ Sc; 1: auto. 
     case pC; 1: smt.
     destruct pC as [j [E1 E2]].
 
    (* we do a case-disjunction on the value of `ck@(pred (A i))` *)
     have pAi := pred_A (pred (A i)) _ _; 1,2: auto.
     case pAi.     
     (* maybe `ck@(pred (A i)) = s`:
        we use `NoCollisionInit` *)
     * destruct pAi as [E3 E4]. 
       rewrite E3 E1 in Collision.
       by have T := NoCollisionInit j _ => //.  
 
     (* or there exists `i0` such that `ck@(pred (A i)) = ck@A i0`:
        we use `NoCollisionA` *)
     * destruct pAi as [i0 [E3 E4]].
       rewrite E3 E1 in Collision.
       have Ord3 : A i0 < A j; 1:smt.
       (* and we conclude by the no collision lemma. *)
       have NC := NoCollisionA i0 j Ord3 _; smt.

   (* B. `$(Oh *> v)` *)
  + have NDedf := base_secrecy (pred Corrupt) _ _; 1,2: auto.
   by apply NDedf.

   (* C. `$(Oh *> ck@t)` *) 
  + by apply base_secrecy.
Qed.


(*------------------------------------------------------------------*)
(* Finally, we prove forward secrecy. *)
global lemma forward_secrecy @set:S/left (t,t':timestamp [const]):
  [happens(t,t')] -> [safe t] -> $( (frame@t') *> (ck@t) ).
Proof.
  intro Hap Safe. 
  have Ded // := simulate_frame t' _.
  deduce with Ded.
  by apply secrecy t. 
Qed.
