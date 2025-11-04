include Core.

hash h.
name k : message.

senc enc,dec.
name r:message.

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
equiv(qatt (qrnd (tau), frame@pred tau)#1, h(diff(u,v),k), enc(diff(u,v),r,k) ).
checkfail prf 1 exn Failure.
checkfail cca1 2 exn Failure.
admit.
clear C.

(* two top level state *)
ghave C : 
equiv( state@tau, state@tau, h(diff(u,v),k), enc(diff(u,v),r,k)).
checkfail prf 2 exn TacticNotPQSound.
checkfail cca1 3 exn TacticNotPQSound.
admit.
clear C.

Abort.



lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
input@tau<>h(zero,k).
Proof.
intro Eq.
have _ : (state@tau,state@tau) = (state@tau,state@tau) by auto.

(* The context does not matter for the reduction to euf here. *)
euf Eq.
Qed.



lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
input@tau<>h(qatt (qrnd (tau), frame@pred tau)#1,k).
Proof.
intro Eq.
checkfail euf Eq exn Failure.
Abort.

lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
qatt (qrnd (tau), frame@pred tau)#1<>h(zero,k).
Proof.
intro Eq.
checkfail euf Eq exn Failure.
Abort.




lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
dec(input@tau,k)<>fail => false.
Proof.
intro Eq.
have _ : (state@tau,state@tau) = (state@tau,state@tau) by auto.

(* The context does not matter for the reduction to euf here. *)
by intctxt Eq.
Qed.


lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
dec(qatt (qrnd (tau), frame@pred tau)#1,k)<>fail => false.
Proof.
intro Eq.
checkfail intctxt Eq exn Failure.
Abort.
