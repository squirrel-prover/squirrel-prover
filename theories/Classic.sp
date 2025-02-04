include Logic.

(*------------------------------------------------------------------*)
(* exec and cond *)

namespace Classic.
  exact lemma [any] exec_not_init (tau:timestamp) :
    init < tau => exec@tau = (exec@pred(tau) && cond@tau).
  Proof.
    intro Ord.
    expand ~def exec@tau.
    auto ~constr.
  Qed.  
  
  exact lemma [any] exec_init (tau:timestamp) : tau = init => exec@tau = true.
  Proof.
    intro Eq.
    expand ~def exec@tau.
    rewrite if_false //.
  Qed.   
  
  exact axiom [any] cond_init (tau:timestamp) : tau = init => cond@tau = true.
  hint smt cond_init.

  exact lemma [any] exec_le (tau,tau':timestamp) : tau' <= tau => exec@tau => exec@tau'.
  Proof.
    induction tau => tau IH Hle Hexec.
    case (tau = tau').
    + auto.
    + intro Hneq.
      rewrite exec_not_init // in Hexec.
      by apply IH (pred(tau)).
  Qed.

 hint smt exec_le.
  
  exact lemma [any] exec_cond (tau:timestamp) : happens(tau) => exec@tau => cond@tau.
  Proof.
    intro Hap Hexec.
    case (init < tau) => _.
    - by rewrite exec_not_init in Hexec.
    - by rewrite cond_init.
  Qed.

  exact lemma [any] executability (t:timestamp):
    happens(t) => 
    exec@t => 
    forall (t0:timestamp), t0 <= t => exec@t0
   .
  Proof.
    intro _ Hexec t0 Hap.
    by apply exec_le t t0.
  Qed.

  hint smt executability.

  exact lemma [any] frame_not_init (tau:timestamp) :
    init < tau =>
    frame@tau = <frame@pred(tau), <of_bool (exec@tau), if exec@tau then output@tau>>.
  Proof.
    intro Neq.
    expand ~def frame@tau.
    auto ~constr.
  Qed.

  exact lemma [any] frame_init :
    frame@init = zero.
  Proof.
    auto.
  Qed.
end Classic.

open Classic.
