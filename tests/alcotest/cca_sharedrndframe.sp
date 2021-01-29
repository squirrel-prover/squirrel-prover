channel c
name sk : message

name n : message
name m : message

name r : index -> message

abstract u : message

senc enc,dec

system !_i (out(c,<diff(n,m), enc(n,r(i),sk)>)).

equiv test.
Proof.
enrich diff(n,m).

induction t.
expandall.
fresh 0.
yesif 0.
by auto.

enrich enc(m,r(i),sk).
expandall.
fa 2; fa 3; fa 3; fa 3.  cca1 3.

admit 2.
Qed.
