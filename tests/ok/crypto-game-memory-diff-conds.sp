include Core.

abstract h: message -> message -> message.

game FOO = {
  oracle foo key = {
    rnd r:message;
    return h key r}}.

channel c.
name r : message
name keyb : message
name keya : message
name ra : message.


process A = 
    in(c,pk);
    out(c,if pk = keyb then h keyb r else empty).

process B = 
   in(c,x);
   out(c, if x = h keyb r then h keya ra else empty).

system (A | B).

global lemma _ (t:timestamp[const]) : 
  [happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto FOO  => //.
+ intro *.
  repeat destruct H0.
  repeat destruct H1.
  destruct H2.
  assert (A < B || B < A) by auto.
  case H2.
  auto.
  auto.
Qed.
