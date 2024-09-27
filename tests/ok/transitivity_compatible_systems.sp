include Basic.

channel c.
abstract b : bool.

process A = 
 in(c,x);
 out(c,x).

process Abis =
  in(c,x);
  if b then out(c,x)
  else out(c,x). 

system FOO1 = A.
system FOO2 = Abis.

global lemma [FOO1] _ (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
checkfail trans [FOO2] exn Failure. (* incompatible systems *)
Abort.

