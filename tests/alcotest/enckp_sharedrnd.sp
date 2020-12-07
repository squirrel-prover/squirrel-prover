channel c
name sk : message
name sk1 : message

name n : message
name m : message

name r : index -> message

abstract u : message

senc enc,dec

system !_i (out(c,<diff(n,m), enc(n,r(i),diff(sk,sk1))>) | out(c,enc(m,r(i),diff(sk,sk1)))).

equiv test.
Proof.
enrich diff(n,m).

induction t.
expandall.
fresh 0.
yesif 0.

expandall.
fa 1. fa 2. fa 2. fa 2.  enckp 2.

admit 2.
Qed.
