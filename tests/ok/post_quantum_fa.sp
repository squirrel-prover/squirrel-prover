include Core.
channel c.

mutable s = empty.

process P = 
  in(c,x); out(c,x).

system [postquantum] PQ = !_i P.



open Quantum.
close Classic.


(* --------------------------------------------------------- *)
(* We should not be able to prove the following lemma, as we are not in the PQ setting. *)
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
    by assumption.
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
    (* Here, notice how frame element number 2 is a classical element, found in frame element 0. 
       It disappears with simpl. *)
    simpl.

    (* We do more fa to get to a state where we only have a single qatt occurence left. *)
    fa 0. 
    {
    have A : forall (t:timestamp), t < P(i) => pred (P(i)) <> pred t  by auto.
      (* the freshness condition has become trivial *)
    by assumption.
    }.
   deduce.   
   by assumption.
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


    (* Here, if we are in the same state as the previous goal. But, instead of doing fa on the qatt()#2, we do it on the qatt()#1 element. Crucially, it is not equivalent. *)
    nosimpl(fa 2).

    (* here, simpl MUST NOT work and eleminate 0, indeed, we have a duplication of a quantum state. *)
    simpl.
    deduce.

    ghave _ :  
  equiv(qatt (qrnd (pred (P(i))), frame@pred (P(i)))#2,
  transcript@pred (P(i)),
  qatt (qrnd (pred (P(i))), frame@pred (P(i)))).
   by admit.  
  assumption.
Qed.
