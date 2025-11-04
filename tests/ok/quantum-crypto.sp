
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
system [postquantum] Q = !_i in(c,x); A: out(c, <x, diff(f x, g x)>).

(* ------------------------------------------------------------------------ *)

(* set verboseCrypto=true. *)

(* Here, we are stuck because we are in classical mode and there are
   quantum computations in the protocol (`qatt`) *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(transcript@tt).
Proof.
  intro H. 
  checkfail by crypto G exn Failure.
Abort.

(* Idem, except that we moreover have to bi-deduce the frame, which is
   a (partially) quantum value. *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(frame@tt).
Proof.
  intro H.
  checkfail by crypto G exn Failure.
Abort.

(* ------------------------------------------------------------------------ *)
(* move to the quantum mode *)
set postQuantumEquivs=true.

(* We succeed now, because we are considering a quantum equivalence *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(transcript@tt).
Proof.
  intro H.
  crypto G. 
Qed.

(* Idem *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(frame@tt).
Proof.
  intro H. 
  crypto G.
Qed.

global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(transcript@tt, frame@tt).
Proof.
  intro H. 
  crypto G.
Qed.

global lemma _ @system:Q (i:_[adv]):
  [happens(A i)] -> equiv(state@A i).
Proof.
  intro H. 
  crypto G.
Qed.

global lemma _ @system:Q (i:_[adv]):
  [happens(A i)] -> equiv(transcript@A i, state@A i).
Proof.
  intro H.
  crypto G.
Qed.

(* with several timestamps *)
global lemma _ @system:Q (t1,t2:_[const]) : 
  [happens(t1)] -> [t1 <= t2] -> 
  equiv(transcript@t1,transcript@t2, frame@t2).
Proof.
  intro H1 H2.
  crypto G. 
Qed.

(* with several timestamps *)
global lemma _ @system:Q (t1,t2:_[const]) : 
  [happens(t1)] -> [t1 <= t2] -> 
  equiv(transcript@t1,transcript@t2, state@t2).
Proof.
  intro H1 H2.
  crypto G. 
Qed.

(* ------------------------------------------------------------------------ *)
(* negative checks *)

(* disable the check ensuring that the exact and approximated
   semantics of top-level terms are equivalent *)
set quantumCheckToplevel=false.

(* duplicated quantum values *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(frame@tt, frame@tt).
Proof.
  intro H. 
  checkfail crypto G exn Failure.
Abort.

(* duplicated quantum values *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(frame@tt, state@tt).
Proof.
  intro H. 
  checkfail crypto G exn Failure.
Abort.

(* duplicated quantum values *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(state@tt, state@tt).
Proof.
  intro H. 
  checkfail crypto G exn Failure.
Abort.

(* cannot use `qrnd` anywhere *)
global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(frame@tt, qrnd tt).
Proof.
  intro H. 
  checkfail crypto G exn Failure.
Abort.

(* ------------------------------------------------------------------------ *)
(* sanity check to make sure that the lemma above goes through if we
   replace `qrnd` by different names *)

name n : timestamp -> quantum_measures_rnd.

global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(frame@tt, n tt).
Proof.
  intro H. 
  crypto G.
Qed.

type T[serializable].
name n2 : timestamp -> T.

global lemma _ @system:Q (tt:_[const]) : 
  [happens(tt)] -> equiv(frame@tt, n2 tt).
Proof.
  intro H. crypto G.
Qed.
