include Logic.

abstract h: message -> message.

game foo = {
oracle foo = {
  rnd r:message;
  return h r}}.

name r : index -> message.

channel c.

name n : message.

process M (i:index) = 
  let m =h n in 
  out(c,h m).

system !_i M(i).


global lemma _ (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto foo.
smt.
Qed.
