channel c.

include Basic.

(* ========================================================= *)
system [E] null.

(* ========================================================= *)
abstract p : index -> message -> bool
abstract m : index -> message -> message -> message

abstract a : message
abstract b : message

name n : message.

game Empty = {}.

system null.

global lemma _ : equiv(if n=a then n else a). 
Proof.
crypto Empty.
Qed.
