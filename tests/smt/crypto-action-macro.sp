include Basic.

set verboseCrypto = true.

abstract a:message.
abstract b:message.
abstract h: message ->  message.

game FOO = {
oracle foo x = {
rnd r:message;
return h diff(<x,r>,b)
}
}.

channel c.
name n : message.

mutable ma:message = zero.

process A = 
ma := h a;
let m = h diff(<ma,n>,b) in 
out(c,m).


process B = 
out(c,h diff(<h a,n>,b)).


system FOO = A | B .


global lemma [FOO] _ (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro Hap.
crypto FOO. 
* auto.
* smt.
* auto.
Qed.
