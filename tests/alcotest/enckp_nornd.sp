channel c
name sk : message
name sk2 : message

name n : message
name m : message

name r : index -> message

abstract u : message

senc enc,dec

system !_i (out(c,<n, enc(n,r(i),diff(sk,sk2))>) | out(c,enc(n,u,sk))).

equiv test.
Proof.
enrich diff(n,m).

induction t.
expandall.
fresh 0.
yesif 0.

expandall.
fa 1. fa 2. fa 2. fa 2. enckp 3.

admit 2.
Qed.
