include Core.
channel c.

mutable s = empty.

process P = 
  in(c,x); out(c,x).

system [postquantum] PQ = !_i P.

open Quantum.
close Classic.

(* --------------------------------------------------------- *)
(* We should not be able to prove the following lemma, as we are not
   in the PQ setting. *)
global lemma [PQ] _ (t:timestamp [const]) :
 [happens(t)] ->  equiv(frame@t).
Proof.
  intro Hap.
  induction t.
  + by expand.
  + rewrite /frame /state. 
    fa 0.
    fa 1. 
    checkfail fa 1 exn Failure.
Abort.

(* --------------------------------------------------------- *)
set postQuantumEquivs = true.

global lemma [PQ] _ (t:timestamp [const]) :
 [happens(t)] ->  equiv(frame@t).
Proof.
  intro Hap.
  induction t.
  + by expand.
  + rewrite /frame /state.
    fa 0.
    fa 1.
    fa 1.
   (* Here, the name is not fresh, as it occures in the transcript ! 
      We should get the following freshness condition, impossible to prove.
    *)
    have A : 
     pred (P(i)) <> pred (P(i)) &&
      forall (t:timestamp), t < P(i) => pred (P(i)) <> pred t 
    by  admit.
    assumption A.
Abort.


global lemma [PQ] _ (t:timestamp [const]) :
 [happens(t)] ->  equiv(frame@t).
Proof.
  intro Hap.
  induction t.
  + by expand.
  + rewrite /frame /state /transcript /exec /cond /output /input .   
    fa 0.
    fa 2.
    fa 3.
    fa 4.
    deduce.

    nosimpl(fa 0). 
    (* Here, notice how frame element number 2 is a classical element,
       found in frame element 0. It disappears with `simpl`. *)
    simpl.

    (* quantum function application on `qatt` *)
    fa 0. 
    {
      have A : forall (t:timestamp), t < P(i) => pred (P(i)) <> pred t  by auto.
      (* the freshness condition is trivial *)
      assumption A.
    }.
    deduce.   
    assumption.
Qed.


global lemma [PQ] _ (t:timestamp [const]) :
 [happens(t)] ->  equiv(frame@t).
Proof.
  intro Hap.
  induction t.
  + by expand.
  + rewrite /frame /state /transcript /exec /cond /output /input .   
    fa 0.
    fa 2.
    fa 3.
    fa 4.
    deduce.

    (* Here, if we are in the same state as the previous lemma. But,
      instead of doing `fa` on `qatt(...)#2`, we do it on `qatt(...)#1`.
      It is not equivalent. *)
    nosimpl(fa 2).

    (* here, `simpl` MUST NOT work and get ride of `0`. Indeed, we have a
      duplication of a quantum state. *)
    simpl.
    deduce.

    ghave E :  
     equiv(qatt (qrnd (pred (P(i))), frame@pred (P(i)))#2,
     transcript@pred (P(i)),
     qatt (qrnd (pred (P(i))), frame@pred (P(i)))).
    by admit.  
    assumption E.
Qed.
