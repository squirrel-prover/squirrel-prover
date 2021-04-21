set autoIntro=false.

channel c
name sk : message

name n : message
name m : message

name r : index -> message

senc enc,dec

system !_i out(c,<diff(n,m), enc(n,r(i),sk)>).

equiv test.
Proof.
enrich diff(n,m).

induction t.
expandall.
fresh 0.
yesif 0. 
auto.

expandall.
fa 1; fa 2; fa 2; fa 2.  cca1 2.

admit 2. 
auto.
Qed.
