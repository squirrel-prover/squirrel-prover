include Deduction.

(* ------------------------------------------------------------------- *)
(* Define a function `get_leq` such that 
   `get_leq (frame@t) t' = frame@t'` when `t' < t`.

   As we cannot (yet) define the function `get_leq` by induction, we
   declare an abstract function and axiomatize it. 

   Notable, each of the axioms below cover one of the case of the
   inductive definition of `get_leq`. *)

op get_leq : message -> timestamp -> message.

axiom [any] get_leq_base t : 
  happens(t) => 
  get_leq (frame@t) t = frame@t.

axiom [any] get_leq_pred t t' : 
  happens(t) => t' < t =>
  get_leq (frame@t) t' = get_leq (frame@pred t) t'.

axiom [any] get_leq_default t t' : 
  happens(t) => t' > t =>
  get_leq (frame@t) t' = zero.

axiom [any] get_leq_no_happens t t' : 
  not (happens(t)) => 
  get_leq (frame@t) t' = zero.

axiom [any] get_leq_no_happens' t t' : 
  not (happens(t')) => 
  get_leq (frame@t) t' = zero.

(* restate and prove the [Deduce.frame_leq] axiom. *)
global lemma frame_leq_bis {P:system} @set:P : 
  $((fun t => frame@t) |1> 
    (fun t t' => if t' <= t then frame@t')).
Proof.
  rewrite /(|1>).
  exists get_leq.
  intro tau.
  apply fun_ext => tau' /=.
  have [?|?|?] : 
     happens (tau, tau') || 
     not (happens tau) || 
     not (happens tau') 
  by auto. 
  * have [A|A|A] : tau' < tau || tau' = tau || tau' > tau by constraints.
    - rewrite if_true //.
      revert A H; induction tau => tau IH H A.
      rewrite get_leq_pred //. 
      case tau' = pred tau. 
      + intro E.  
        rewrite E.
        by apply get_leq_base.
      + by intro ?; apply IH. 
    - rewrite A in *; clear A. 
      rewrite if_true //.
      by apply get_leq_base.
    - rewrite if_false //.
      by rewrite get_leq_default.
  * rewrite if_false //.
    by apply get_leq_no_happens.
  * rewrite if_false //.
    by apply get_leq_no_happens'.
Qed.
