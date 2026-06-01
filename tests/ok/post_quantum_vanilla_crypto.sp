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
[happens(tau)] -> equiv(frame@tau) -> equiv(frame@tau, h(diff(u,v),k)).
Proof.
intro t E. 
prf 1.
by fresh 1; assumption.
Qed.

global lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
[happens(tau)] -> [false].
Proof.

intro T.
(* unsynced qrn *)
ghave C : 
equiv(qatt (qrnd (tau), frame@pred tau)#1, h(diff(u,v),k), enc(diff(u,v),r,k) ).
checkfail prf 1 exn Failure.
checkfail cca1 2 exn Failure.
admit.
clear C.

(* two top level state *)
ghave C : 
equiv( frame@tau, frame@tau, h(diff(u,v),k), enc(diff(u,v),r,k)).
checkfail prf 2 exn Failure.
checkfail cca1 3 exn Failure.
admit.
clear C.

Abort.



lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
happens(tau) => input@tau<>h(zero,k).
Proof.
intro H Eq.
have _ : (state@tau,state@tau) = (state@tau,state@tau) by auto.

(* The context does not matter for the reduction to euf here. *)
euf Eq.
Qed.



lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
happens(tau) =>  input@tau<>h(qatt (qrnd (tau), frame@pred tau)#1,k).
Proof.
intro H Eq.
checkfail euf Eq exn Failure.
Abort.

lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
happens(tau) =>   qatt (qrnd (tau), frame@pred tau)#1<>h(zero,k).
Proof.
intro H Eq.
checkfail euf Eq exn Failure.
Abort.




lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
happens(tau) => dec(input@tau,k)<>fail => false.
Proof.
intro H Eq.
have _ : (state@tau,state@tau) = (state@tau,state@tau) by auto.

(* The context does not matter for the reduction to euf here. *)
by intctxt Eq.
Qed.


lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
happens(tau) =>  dec(qatt (qrnd (tau), frame@pred tau)#1,k)<>fail => false.
Proof.
intro H Eq.
checkfail intctxt Eq exn Failure.
Abort.


gdh g, (^) where group:message exponents:message.

name a : message

name b : message

name d : message.

lemma [set: PQ; equiv: PQ]  _ tau : input@tau <>g^a^b.
Proof.
 intro Eq. 
 checkfail cdh Eq, g exn TacticNotPQSound.
 checkfail gdh Eq, g exn TacticNotPQSound.
 Abort.
