

channel c
name sk : message

name n : message
name m : message

name r : index -> message

abstract u : message

senc enc,dec

system !_i (out(c,<diff(n,m), enc(n,r(i),sk)>) | out(c,enc(m,r(i),sk))).

equiv test.
Proof.
enrich diff(n,m).

induction t; try auto.
expandall.
by fresh 0.

expandall. 
fa 1; fa 2; fa 2. 
fa 2.  
cca1 2.

Qed.
