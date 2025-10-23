include Core.
close Classic.
open Quantum.

(* ------------------------------------------------------------------------ *)
op f : message -> message.
op g : message -> message.

game G = {
  oracle o x = { return diff(f x, g x); }
}.


(* ------------------------------------------------------------------------ *)
channel c.

system [classic] C = !_i in(c,x); out(c, <x, diff(f x, g x)>).

(* ------------------------------------------------------------------------ *)
(* In the classical setting, works without trouble *)
global lemma _ @system:C (tt:_[const]) : [happens(tt)] -> equiv(Classic.frame@tt).
Proof.
  intro H.
  crypto G.
Qed.

(* ------------------------------------------------------------------------ *)
system [postquantum] Q = !_i in(c,x); out(c, <x, diff(f x, g x)>).

(* ------------------------------------------------------------------------ *)

(* set verboseCrypto=true. *)

(* Here, we are stuck because we are in classical mode and there are
   quantum computations in the protocol (`qatt`) *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.transcript@tt).
Proof.
  intro H. 
  checkfail by crypto G exn GoalNotClosed.
Abort.

(* Idem, except that we moreover have to bi-deduce the frame, which is
   a (partially) quantum value. *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.frame@tt).
Proof.
  intro H.
  checkfail by crypto G exn GoalNotClosed.
Abort.

(* ------------------------------------------------------------------------ *)
(* move to the quantum mode *)
set postQuantumEquivs=true.

(* We succeed now, because we are considering a quantum equivalence *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.transcript@tt).
Proof.
  intro H.
  crypto G. 
Qed.

(* Idem *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.frame@tt).
Proof.
  intro H. 
  crypto G.
Qed.

(* ------------------------------------------------------------------------ *)
(* negative checks *)

(* disable the check ensuring that the exact and approximated
   semantics of top-level terms are equivalent *)
set quantumCheckToplevel=false.

(* duplicated quantum values *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.frame@tt, Quantum.frame@tt).
Proof.
  intro H. 
  checkfail crypto G exn Failure.
Abort.

(* duplicated quantum values *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.frame@tt, Quantum.state@tt).
Proof.
  intro H. 
  checkfail crypto G exn Failure.
Abort.

(* duplicated quantum values *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.state@tt, Quantum.state@tt).
Proof.
  intro H. 
  checkfail crypto G exn Failure.
Abort.

(* cannot use `qrnd` anywhere *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.frame@tt, qrnd tt).
Proof.
  intro H. 
  checkfail crypto G exn Failure.
Abort.

(* ------------------------------------------------------------------------ *)
(* sanity check to make sure that the lemma above goes through if we
   replace `qrnd` by different names *)

name n : timestamp -> quantum_measures_rnd.

global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.frame@tt, n tt).
Proof.
  intro H. 
  crypto G.
Qed.

type T[serializable].
name n2 : timestamp -> T.

global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(Quantum.frame@tt, n2 tt).
Proof.
  intro H. crypto G.
Qed.
