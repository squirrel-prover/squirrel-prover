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
name m : index -> message.

process A = 
let ma = h a in
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
* smt ~prover:Z3.
* auto.
Qed.


process C (i:index) = 
let ma = h a in 
let m = h diff(<ma, m i>,b) in 
out(c,m)

process D (i:index) = 
out(c, h diff(<h a, m i>,b)).

system FOO2 = (!_i (C i)) | (!_j (D j)) .


global lemma [FOO2] _ (t:timestamp[const]):
[happens(t)] -> equiv(frame@t).
Proof.
intro Hap.
crypto FOO. 
* auto.
* smt ~prover:Z3.
* auto.
Qed.
