
include Basic.

name a:message.
name b:message.

channel c.

process A = 
  let msg= diff(a,b) in
  out(c, msg).

process Abis = 
  let msg = diff(a,b) in
  out(c,msg).

system S1= A.
system S2= Abis.

process B = 
  out(c, diff(a,b)).

process Bbis = 
  out(c,diff(a,b)).

system SB1= B.
system SB2= Bbis.

game FOO = {
   oracle foo = {
    rnd a:message;
    rnd b:message;
    return diff(a,b)}
}.

global lemma [SB1/left,SB2/right] _ (t:timestamp[const]) : 
[happens(t)] -> 
equiv(frame@t).
Proof.
intro *.
crypto FOO => //.
Qed.

global lemma [SB1/left,SB2/right] _ (t:timestamp[const]) :
[happens(t)] ->
equiv(diff(a,b),frame@t).
Proof.
intro *.
crypto FOO => //.
Abort.


global lemma [S1/left,S2/right] _ (t:timestamp[const]) : 
[happens(t)] -> 
equiv(frame@t).
Proof.
intro *.
crypto FOO => //.
Qed.
