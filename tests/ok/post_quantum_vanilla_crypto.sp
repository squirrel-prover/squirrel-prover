include Core.

hash h.
name k : message.

set postQuantumEquivs=true.

system [postquantum] PQ = null.

close Classic.
open Quantum.

abstract u : message.
abstract v : message.

global lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
equiv(frame@tau) -> equiv(frame@tau, h(diff(u,v),k)).
Proof.
intro E.
prf 1.
by fresh 1; assumption.
Qed.

global lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
[false].
Proof.


(* unsynced qrn *)
ghave C : 
equiv(qatt (qrnd (tau), frame@pred tau)#1, h(diff(u,v),k)).
checkfail prf 1 exn TacticNotPQSound.
admit.
clear C.

(* two top level state *)
ghave C : 
equiv( (state@tau, state@tau, h(diff(u,v),k)) ).
checkfail prf 1 exn TacticNotPQSound.
admit.
clear C.

Abort.
