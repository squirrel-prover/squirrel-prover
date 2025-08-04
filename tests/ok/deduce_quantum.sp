(* Test that the deduction engine (used notably in `deduce` and
   `apply`) does not violate the no-cloning theorem. *)

include Core.

system [postquantum] Q = null.

set postQuantumEquivs=true.

axiom foo @system:any ['a] (x : 'a) : x = (x,1)#1.

global lemma _ @system:Q (x : quantum_message) : 
  equiv(x,x).
Proof. 
  deduce.                       (* `deduce` should leave `1` unchanged *)
  rewrite foo in 1. (* check that item `1` still exists *)
Abort.

global lemma _ @system:Q (x : quantum_message) : 
  equiv(x) -> equiv(x,x).
Proof.
  intro E. 
  checkfail apply E exn ApplyMatchFailure.
Abort.

global lemma _ @system:Q (x : quantum_message) : 
  equiv(x) -> equiv(x,x).
Proof.
  intro E. 
  checkfail deduce 1 exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* test that deduction correctly implements the binder rule *)

global lemma _ @system:Q (x : quantum_message) : 
  equiv(x) -> equiv(fun (_ : index) => x).
Proof.
  intro E. 
  checkfail apply E exn ApplyMatchFailure.
Abort.

global lemma _ @system:Q (x : quantum_message) : 
  equiv(x, fun (_ : index) => x).
Proof. 
  checkfail deduce 1 exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* test the `assumption` tactic *)
global lemma _ @system:Q (x : quantum_message) :
  equiv(x) -> equiv(x,x).
Proof.
  intro E. 
  checkfail assumption E exn NotHypothesis.
Abort.

