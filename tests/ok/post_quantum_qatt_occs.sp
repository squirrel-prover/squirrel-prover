include Core.


set postQuantumEquivs=true.

system [postquantum] PQ = null.

close Classic.
open Quantum.

global lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
equiv(frame@tau).
Proof. admit. Qed.


global lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
[happens(tau)] -> equiv(frame@tau).
Proof. admit. Qed.


(* we can provide several time the classical part of the computation. *)
global lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
equiv(qatt (qrnd (pred tau), frame@pred tau)#1,
      qatt (qrnd (tau), frame@tau)#1,
      qatt (qrnd (tau), frame@tau)#1
     ).
Proof. admit. Qed.
 


