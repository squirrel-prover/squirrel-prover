channel c.
process A = out(c,witness).
system toto = A.


lemma _ @system:toto : true.
Proof.
  set ? := witness = 1.
  set ? := 1 = witness.
  set ? := (input@A = witness).
  set ? := (witness = input@A).
  set ? := (input@A = witness[message]).
Abort.
