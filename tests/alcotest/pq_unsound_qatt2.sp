include Core.


set postQuantumEquivs=true.

system [postquantum] PQ = null.

close Classic.
open Quantum.


(* Not PQ, we check that qrn t is always used when given frame@t as argument. *)
global lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
equiv(qatt (Quantum.qrnd (pred tau), Quantum.frame@tau )).
