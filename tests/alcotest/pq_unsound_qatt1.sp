include Core.


set postQuantumEquivs=true.

system [postquantum] PQ = null.

close Classic.
open Quantum.

abstract u : message.

(* Cannot have two distinct quantum types at top level *)
global lemma [set: PQ; equiv: PQ]  _ (tau:timestamp [const]):
equiv(frame@tau, frame@tau, u).
