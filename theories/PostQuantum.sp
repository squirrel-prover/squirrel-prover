(*------------------------------------------------------------------*)
(* exec and cond *)

namespace Quantum.
  close Classic.
  
  (* Squirrel can only expand exec for specific actions.
     This axiom allows to go beyond this. It would be provable
     in any system, by performing a case analysis on tau. *)
  axiom [any] exec_not_init (tau:timestamp) :
    init < tau => exec@tau = (exec@pred(tau) && cond@tau).
  
  axiom [any] exec_init (tau:timestamp) : tau = init => exec@tau = true.
  axiom [any] cond_init (tau:timestamp) : tau = init => cond@tau = true.
  
  lemma [any] exec_le (tau,tau':timestamp) : tau' <= tau => exec@tau => exec@tau'.
  Proof.
    induction tau => tau IH Hle Hexec.
    case (tau = tau').
    + auto.
    + intro Hneq.
      rewrite exec_not_init // in Hexec.
      by apply IH (pred(tau)).
  Qed.
  
  lemma [any] exec_cond (tau:timestamp) : happens(tau) => exec@tau => cond@tau.
  Proof.
    intro Hap Hexec.
    case (init < tau) => _.
    - by rewrite exec_not_init in Hexec.
    - by rewrite cond_init.
  Qed.
  
  axiom [any] executability (t:timestamp):
   happens(t) => 
    exec@t => 
    forall (t0:timestamp), t0 <= t => exec@t0.
end Quantum.
