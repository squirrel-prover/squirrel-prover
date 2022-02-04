channel c.

(*------------------------------------------------------------------*)
abstract ok : message.

system [test] (A: out(c, ok); B: out(c, ok)).

system [test2] (A: out(c, ok)).

(* action `B` does not exists in the system `test2` *)
goal [test2] _ (i,j : index) : false.
Proof.
  try (assert(output@B = ok) by auto).
Qed.


